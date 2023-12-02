variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118863468387068442147961537823 : ((True → (((p5 ∨ (False ∧ p1)) → p3) ∧ ((p4 ∨ (((p1 ∧ ((p4 ∨ p2) ∧ p3)) ∧ p5) ∧ ((p4 → p5) ∧ p5))) ∧ p4))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262151266734405313208595146968 : (True ∧ ((((p1 ∧ (((((p3 ∨ p5) ∧ True) ∨ (p5 ∧ p2)) ∨ ((p5 → p5) → (p2 ∧ p1))) ∨ p1)) ∨ (True ∨ (p3 → p3))) ∨ p3) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172661483124560846872642592553 : (((False → p1) ∧ (((False → ((p4 ∧ p2) ∨ p2)) ∨ (p1 ∨ p3)) → (p1 ∨ p3))) ∨ ((((True → p5) ∧ p5) ∨ False) ∨ ((False ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66194510015121142416422957877 : ((p5 ∨ ((((p3 → (p4 → (True ∨ False))) ∨ ((False ∨ (False ∧ False)) ∨ p5)) → (p2 ∨ p3)) ∨ ((((p4 → p2) ∧ p4) ∧ p2) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617923617232813886434120203180 : (((((p4 ∧ (p1 ∨ ((p3 → p1) → p1))) → (p4 → (False ∧ (False ∧ (((True ∨ ((p2 → False) ∧ p3)) ∧ (True ∧ p3)) ∨ True))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184421031866505385282412868793 : ((((((p1 → p1) ∨ True) → p1) ∧ (p4 ∧ p4)) ∧ (True ∨ p1)) ∨ (((True ∧ p3) → ((((p5 → (p2 → p4)) ∨ p1) → p3) ∨ p1)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117625527226371697307069810452 : ((p3 ∧ ((p5 ∨ (((p1 ∧ (p5 ∨ ((True → p3) ∨ p4))) ∨ ((True → p5) → ((True ∨ (False ∨ True)) ∧ p3))) → False)) ∧ p5)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114857613419995108022635596662 : ((((((p3 ∧ p4) ∧ ((p1 ∨ p3) ∨ False)) ∨ (p5 ∨ p4)) ∧ (False ∧ p3)) ∨ (((True ∨ p4) ∨ True) → ((p5 ∨ p4) → True))) ∨ (False ∨ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147716707149487446648843849075 : ((((p3 → (((p1 ∨ True) → p5) → (p1 ∨ p3))) ∧ (((((p3 ∨ p4) ∨ False) ∨ True) ∨ p2) → p5)) → p1) ∨ ((p4 → p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350174158570285873435990541807 : (p4 → ((((p3 ∨ ((p4 ∨ p3) → p3)) → p4) → ((p3 ∨ ((p1 → ((False ∧ p3) ∨ p5)) ∧ (p5 ∧ (p4 → False)))) → (p2 ∨ p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349701162665348940782123469869 : (p4 → (((((True ∧ p1) → (((p1 ∨ p5) ∨ p2) ∧ ((p1 → p3) → p2))) ∨ (p5 ∨ True)) → ((((p2 ∧ p3) → False) ∨ True) ∨ True)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600599153950585884387508890150 : ((((True ∧ (p4 → ((((p5 ∨ p3) ∧ (p1 ∧ p5)) ∨ p5) ∧ (p3 → ((p4 → p2) ∨ ((((p3 → False) ∧ p4) → p2) → p1)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629072627803984923167724176691 : ((((((((p4 ∨ (((False ∧ (False → p3)) ∨ p4) ∧ (p1 ∨ ((False ∧ (p1 → (p1 ∨ False))) ∨ False)))) ∧ p3) ∨ p3) ∨ p4) ∨ p2) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741299107921557100247390353617 : ((((p4 ∨ p5) ∨ ((((False ∨ (True → (False ∨ (p2 ∧ p1)))) ∨ p2) ∧ (((False → (True → ((p3 ∧ p3) ∧ p4))) ∨ p3) ∧ p5)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_42162759734195922567078886378 : ((((p3 → p4) → ((p5 ∨ (p4 → p3)) ∨ (p5 ∨ ((p1 ∧ ((True ∨ False) ∨ p5)) ∧ ((p2 ∨ (False → (p5 ∨ True))) → False))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233656905172678274320071280419 : ((p2 ∨ (p3 ∨ p4)) → ((False ∨ ((p2 ∧ (p1 → (p5 ∧ (((p4 ∨ ((False → (p3 → False)) ∨ True)) ∧ (p4 ∨ False)) → p4)))) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804025429514706011519963889343 : (((p3 → ((p1 ∨ (((True → ((False ∧ p3) → p2)) ∧ p5) ∨ (((False ∨ p3) → (False ∧ (False ∨ p1))) ∨ False))) ∨ (p4 → (False ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731479106634662190974893509149 : ((((True → (True → p4)) → ((p4 → (((p5 ∨ (True ∧ (p4 → False))) ∨ p1) → p5)) ∨ (p2 ∨ ((p1 ∧ p1) → ((False ∧ p4) ∨ p4))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312030071749636190010408970908 : (p2 ∨ (p4 ∨ (p1 ∨ (((((True ∨ p2) ∨ (True ∧ p2)) ∧ p3) ∧ (p4 ∧ True)) ∨ (False → (False ∨ (False ∧ ((True → (p5 ∨ False)) → p5)))))))) := by
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
theorem thm_5_vars_191141997553996906693887940137 : ((((p3 ∧ p5) ∨ False) ∨ (((p2 ∨ p3) ∨ False) ∧ p3)) ∨ ((p2 → (True → ((p2 ∨ p5) ∨ (False ∨ p1)))) ∨ (p2 → (p3 ∧ (p2 ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246427006655149935471050937799 : ((p5 ∧ True) ∨ (p4 → ((p5 ∧ ((((p5 ∨ False) ∨ True) ∨ p4) ∧ (True → ((p4 ∧ ((p4 → p5) ∧ p3)) ∧ ((False ∧ p2) ∧ p4))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148929770501540031329548332125 : ((((p2 → False) ∨ (False ∧ True)) → (p5 → (p1 ∨ (True ∧ (p5 → ((p5 ∨ p2) → (True → (p4 ∧ p1)))))))) ∨ ((p5 ∧ p1) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181450554741738205587195227377 : ((p3 ∨ (p5 ∧ ((True ∧ (p3 → ((p3 ∧ p2) ∨ p3))) ∨ (p1 ∨ p2)))) → (p5 → ((((p2 ∨ p3) ∨ p4) → p1) ∨ (p5 ∨ (True ∧ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716189926737063098394523637860 : (((((p5 ∧ (p5 → p3)) → False) ∧ (True ∧ ((((p5 → (p4 ∧ p4)) ∧ (p2 → p5)) → p2) ∧ (p4 → (((p5 → True) ∧ p1) ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66081365638868995388768529792 : ((p5 ∨ ((p5 ∨ (p2 ∨ (((p5 → ((p3 ∧ (p4 ∨ (p2 → True))) → p4)) ∧ p2) → (((p3 → False) ∨ p4) → (p3 → p4))))) ∨ p1)) ∨ False) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130434490460948384033512549258 : (((((True ∧ (((True → (p3 → False)) ∧ (p4 → p1)) ∧ True)) ∨ p3) ∧ ((p2 ∨ p3) ∧ p1)) ∨ ((p2 ∨ p5) ∨ True)) ∧ (False → (p1 ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346489323320182828481900967898 : (p3 → ((p3 ∧ (((((p5 → p2) ∧ ((p4 ∨ (p1 → ((True ∧ p4) → p3))) → (p4 ∨ (False → p3)))) ∨ False) → False) ∧ p2)) → (False ∧ p1))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (((p5 → p2) ∧ ((p4 ∨ (p1 → ((True ∧ p4) → p3))) → (p4 ∨ (False → p3)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h13 := h5 h7
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h2.left
  let h15 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h18 : (((p5 → p2) ∧ ((p4 ∨ (p1 → ((True ∧ p4) → p3))) → (p4 ∨ (False → p3)))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h19
    -- One of the premise coincides with the conclusion.
    exact h17
    -- Implications on the right can always be decomposed.
    intro h20
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h24 := h16 h18
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263885238168355927820685013827 : (True ∧ (((p5 → ((((p5 → (p5 ∧ False)) → p4) ∧ p4) → (True → p3))) ∨ p4) ∨ ((False ∧ p3) → ((p1 → p4) ∧ (True → (True ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203081390281471091254090141753 : (((True → p4) → ((p2 → p2) ∧ True)) ∧ ((p4 ∨ p1) → (((p3 ∨ (p5 ∨ p2)) → p1) ∨ ((True ∧ (True → (p2 ∧ (p3 ∨ p1)))) ∨ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117369765173251234484050855191 : ((False ∧ (True → (False ∨ ((p4 ∧ (((p5 ∧ p2) → ((p3 → (p3 ∨ (((p2 → p4) → False) → p1))) ∧ p1)) → p2)) ∧ True)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641732551991125207113648581525 : (((((p3 ∨ True) → ((((p2 ∨ p3) → (True ∧ (p1 ∨ ((((p2 → p3) ∨ (p1 ∨ p1)) ∨ p1) ∨ False)))) → (True ∧ p4)) ∧ p3)) → p3) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679434108427595089041306694315 : ((((((((((p1 ∧ p3) ∧ True) → (p3 ∨ ((False ∨ False) → (p1 ∨ True)))) ∨ p4) ∧ p5) ∧ p5) ∧ p1) → (p4 ∧ (p2 → (False ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697413987874018515910361830943 : ((((False ∧ ((((p4 ∧ p1) ∨ p1) → (False ∧ (p5 ∨ False))) ∧ p1)) ∧ (True → (p5 ∧ (((((p5 ∧ True) ∨ p5) ∧ p2) → p5) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339500686829536887471260754591 : (p1 → (False ∨ ((((((p1 → (p4 → (p1 → (p4 → (p3 ∨ p5))))) → p5) ∨ p1) ∨ p2) ∨ False) ∨ (False ∨ (p1 → ((True ∨ True) ∧ False)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168323253569040210574240390713 : (((p2 → p1) ∧ (p2 ∧ ((p3 → p3) ∧ (((False ∨ (p4 → (p4 → p4))) ∨ True) → p5)))) → ((((p3 → False) ∨ True) ∧ (p5 ∧ p1)) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219818577346830557445418690174 : ((p3 → ((p3 ∨ False) ∧ p3)) → ((((p4 → ((True ∨ False) ∨ p4)) ∧ ((False ∧ False) ∨ p4)) → p4) → (((p4 ∧ (p5 ∧ True)) → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179112119463808887756320498811 : ((False ∧ (p2 ∨ (p1 ∧ ((((p5 ∨ p3) → p5) ∧ p3) ∨ (p5 ∧ p2))))) ∨ (p3 ∨ ((True ∧ True) → (p1 → (p2 → (False ∨ (p2 ∧ p1))))))) := by
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
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681586881054737330758199171078 : ((((p1 → ((True ∧ p4) ∧ (False → (((((p4 → p5) ∧ (p3 ∨ (p1 ∧ p1))) → True) ∨ True) ∨ p4)))) → (p5 ∧ ((p1 ∧ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39295018706917294993725020765 : (((p1 ∧ (((p5 ∨ ((p1 ∨ True) ∨ False)) → True) ∧ ((((p5 ∧ (True → p4)) ∨ False) ∧ p1) ∨ (((True → True) → p5) → False)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356022679916474799062631678379 : (p5 → ((((p1 ∧ (p3 ∨ p2)) → ((p4 → ((False ∧ p5) ∧ (p5 ∨ True))) → (False ∨ p2))) ∨ (p3 ∨ p4)) ∨ (False → (p1 ∨ (p4 ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68444715558400404501744899867 : ((p3 → (False ∧ (((p2 ∨ ((p5 ∨ ((False ∧ ((p5 → ((p2 ∧ p5) ∧ (p5 ∨ (True ∧ p5)))) ∨ p3)) ∨ p5)) → p4)) → p2) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138508569439168809610970998226 : ((((p5 ∨ (((True ∨ p3) → ((((False ∧ p2) ∧ (p5 ∨ p3)) ∨ ((p4 → p3) ∨ p4)) ∧ p3)) → p5)) ∧ p1) ∧ p3) → ((p1 → p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((True ∨ p3) → ((((False ∧ p2) ∧ (p5 ∨ p3)) ∨ ((p4 → p3) ∨ p4)) ∧ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h17 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314027091979055105192323776239 : (p3 ∨ ((True → (p1 → ((((p4 ∨ (p4 → ((p2 → True) → (p5 → (((p4 → False) ∧ p4) ∧ p2))))) ∨ p2) ∧ False) ∨ p2))) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49764062091591659591953484045 : (((False ∨ (((p5 ∧ True) → (p1 → (False ∨ p2))) → (((False → ((p1 ∧ p2) ∧ p5)) → (p1 ∧ False)) ∧ p3))) → (True → (p5 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191673610792992009435972659838 : ((p5 ∧ (((True ∨ (p1 ∧ p2)) → True) ∨ (p5 → p3))) ∨ (False ∨ (p2 → ((p4 ∨ ((False ∧ p3) ∨ True)) ∧ ((p2 → (p1 ∨ p2)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64970230983091680276313607413 : ((p2 ∨ (((p4 → (p1 → (False ∧ True))) ∨ p3) → (((((p5 ∨ False) ∨ p3) → True) → ((p1 → False) → p2)) ∨ ((p5 ∨ True) ∨ p5)))) ∨ p4) := by
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
theorem thm_5_vars_263984500268046063020015294171 : (True ∧ (((p3 ∨ (True → p4)) ∧ ((p1 ∨ (p4 ∨ (p3 ∨ False))) ∨ p2)) ∨ (((((p2 → (True ∧ p1)) ∨ True) ∨ (p5 ∧ True)) ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63095688900888863144008858313 : ((p5 ∧ (((p1 ∨ p1) ∧ (p1 → ((p1 ∨ p5) → (False ∨ (True ∧ (False ∧ (p5 → ((p5 → p1) ∧ (p3 ∨ (p5 ∧ False)))))))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800982996464286099099857789197 : (((p2 → ((((((((p1 ∧ True) ∨ p3) ∨ True) → p2) → (p1 ∧ ((p3 ∨ True) ∨ p5))) ∧ p5) ∨ (True ∨ p1)) ∧ (p5 → (p3 ∨ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698876571665125572772830430444 : ((((p1 ∧ ((False ∨ ((True → p3) → True)) ∧ ((p5 → False) ∧ True))) ∨ ((((p4 ∧ False) ∨ p1) ∨ True) → (p3 → ((p4 ∧ p2) ∨ True)))) ∨ p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700065462141301342892916038173 : ((((((p2 → p1) ∨ False) ∨ (p2 → (p3 ∨ ((p4 → p5) ∧ True)))) → (((False ∨ (p4 → (p3 → False))) ∧ False) ∨ (p4 → (p5 ∨ True)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56161498688153921719105772015 : (((False ∧ ((p3 ∨ p5) ∨ True)) ∨ ((True → (False → True)) ∧ ((p4 ∨ p2) ∨ ((p2 ∨ ((False ∧ p1) ∧ ((True ∧ p2) ∧ p1))) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620162092826605954972499672821 : (((((p2 ∧ False) ∨ ((((p5 ∨ p1) → p2) ∨ p4) ∧ (p5 → ((p2 → (((((p1 → p1) ∨ p3) → True) ∨ p5) ∨ p1)) ∨ True)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40168856523268655196017444769 : (((((p5 ∧ (p4 ∨ (p2 ∧ ((p5 → False) → p5)))) → ((p5 ∨ ((p3 → p5) ∨ False)) ∧ (p1 ∨ ((p5 → p1) ∧ p3)))) ∧ p5) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135777534101169418417418903485 : ((((((p1 → p5) ∨ (p5 ∨ (p1 → p2))) ∧ ((p4 ∧ False) ∧ p3)) → p1) → (p2 → (p1 → (p2 ∨ (p2 ∨ p3))))) ∨ ((False → True) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115205152657202103431440251271 : (((p1 ∧ (p3 ∨ ((p2 → (p5 ∧ (True → p5))) ∧ p1))) ∧ (p3 ∨ (True ∧ ((True ∨ p3) → ((True → (False ∧ True)) ∨ p3))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310658553196178593464801041845 : (p2 ∨ ((((p1 → p3) ∨ p1) ∨ False) → (((((p1 → (p3 ∨ p5)) ∧ p1) → (((p1 ∨ p4) ∧ (p2 ∧ p3)) ∧ p5)) → (p1 ∧ p3)) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194118119338126608137520415760 : ((False → (p1 ∧ (((p3 ∨ (False ∨ p3)) ∧ True) ∧ p3))) → (((p3 → True) ∧ p1) → (((p1 ∨ p4) ∨ ((p3 → (p1 ∨ p4)) → True)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53469127705090262538528815079 : ((((False → p5) → ((False ∧ (True ∧ p1)) ∧ ((p3 ∧ p3) → True))) → (((((p1 ∧ True) → p1) → (True ∧ p2)) ∨ (p5 ∧ p3)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113812953588330514680828331658 : (((p1 ∧ ((p1 ∧ p1) → ((((True → p1) ∧ (((p5 ∨ False) → p2) ∧ p2)) ∨ ((p5 ∧ p4) ∨ p2)) ∨ p2))) → (p4 ∨ p2)) ∨ (p1 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∧ p1) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177639277082327811300252702914 : ((((False ∧ (((False ∨ (p1 ∨ True)) ∨ (False → False)) ∨ p4)) ∧ p3) ∧ p3) ∨ ((False → (False ∨ (True → True))) ∧ (True → ((p4 ∧ p2) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116715672844590528246845173986 : (((p2 ∧ False) ∨ ((p1 ∧ ((p3 ∨ ((p2 → ((p4 → (p5 ∧ (p2 → p1))) ∧ True)) ∧ p2)) ∨ p5)) ∨ ((p5 ∧ p5) ∧ p1))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105741692017925414135534069640 : ((((p5 ∨ p3) ∨ ((True ∧ (p1 → p4)) → ((True ∧ p1) ∨ (False ∧ (p1 ∧ p5))))) ∨ (True ∧ ((p5 → (p5 ∧ True)) ∨ p1))) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259748039653433874659211584122 : ((p1 → p2) → ((False ∨ (p1 ∨ (p5 ∨ ((p3 ∨ False) → ((p5 ∨ p4) ∨ (((False ∨ True) ∨ False) ∨ ((p4 → p4) ∧ p2))))))) ∨ (p1 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49160003340009562747719146650 : (((((p1 ∧ ((p1 ∨ p2) → p2)) ∧ p4) ∧ ((False → (p1 → (p1 ∨ ((p5 → (True ∧ p3)) ∨ True)))) ∨ False)) ∨ ((p5 ∨ p2) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178792160151715711875912479984 : ((((p2 ∨ p2) ∧ p4) ∨ (p4 ∨ (p2 → (((True ∧ p2) → p4) ∨ p2)))) ∨ ((p2 ∨ ((p4 ∨ p2) ∧ (False → ((False ∨ p2) → p5)))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114369409175845446044141794867 : ((((((p5 ∨ p2) ∧ ((p5 → True) ∧ False)) ∨ (p2 ∧ (p3 ∨ ((p2 ∨ p4) → p4)))) ∨ p5) ∨ ((p3 ∨ (p4 → p2)) → p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130412233081614075351733777758 : ((((False ∨ ((p2 ∨ p3) ∨ (False ∧ (p4 → (((p5 ∨ (p2 → p5)) ∧ p5) → False))))) ∧ p4) ∨ (False → (p1 → p4))) ∧ (p2 → (p3 ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61170699075352234678363373215 : ((False ∧ ((p5 ∧ (p5 ∨ p5)) ∨ (((False ∨ (p5 ∧ (False → p2))) ∨ (p3 ∨ p3)) → ((False ∧ ((p3 → p2) ∨ (p3 ∧ p1))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322259891084967731251919775492 : (p5 ∨ (((((False ∨ p3) ∨ False) ∨ (p1 ∧ (False → (p2 ∨ (p2 ∨ ((True ∨ p3) → ((((p3 ∧ p3) ∧ False) → p5) → True))))))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115830211145832856894103744365 : ((((True → True) → (True → p4)) ∧ (((((True ∨ True) ∨ p4) ∨ ((False → p4) → (False ∧ p5))) ∧ p5) → ((True → True) → p1))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678516850869501539900858702289 : ((((((p1 ∧ p2) ∧ p5) ∨ ((((True ∧ (p5 ∨ p3)) ∧ (True ∨ (p2 ∧ (p2 → p4)))) → p2) ∧ p2)) ∨ ((p3 ∨ True) → (True → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262274890884986825263544030750 : (True ∧ (((p3 ∨ (((p2 → p4) → ((True → p3) → p5)) ∨ ((p1 → (p1 ∧ (p2 → True))) ∨ False))) ∨ (p4 ∨ ((p1 → p3) ∨ p1))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55480615244290468817638657964 : (((((p3 → p2) → p1) ∨ (p4 ∧ p5)) → (((p3 → (((((p1 → False) → p3) ∧ p2) ∨ (p3 ∧ p3)) ∨ True)) → False) → (p1 → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p3 → (((((p1 → False) → p3) ∧ p2) ∨ (p3 ∧ p3)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p3 → (((((p1 → False) → p3) ∧ p2) ∨ (p3 ∧ p3)) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h11
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628046920501425567164034717082 : ((((((True ∨ (p4 ∧ (p1 → p2))) ∧ (p3 ∧ (((p4 → (((p3 ∧ p1) ∧ True) → p5)) ∨ ((p5 → True) ∨ p2)) → False))) ∧ p2) → False) ∨ p4) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((p4 → (((p3 ∧ p1) ∧ True) → p5)) ∨ ((p5 → True) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h5.left
    let h16 := h5.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : ((p4 → (((p3 ∧ p1) ∧ True) → p5)) ∨ ((p5 → True) ∨ p2)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h17
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354419676386610274505831566255 : (p5 → (((p3 ∧ True) ∨ ((((p4 → p5) ∨ ((p1 → ((False ∧ ((True ∧ p4) → p1)) → True)) → p5)) → (p1 ∧ False)) ∨ (False → True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62634608249771960079963187238 : ((p4 ∧ ((False ∧ ((p5 → (((False ∧ (p3 ∨ p5)) ∧ ((p5 ∧ p5) ∨ p1)) ∨ ((p1 → p2) ∧ p2))) → (p1 ∨ (p1 ∨ p3)))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340201494348927026662579721463 : (p1 → (p4 → (p4 → ((((p4 → (False ∨ p1)) → ((False → p3) → p2)) ∧ False) ∨ (p5 → ((((p1 ∧ p4) ∨ p5) → p5) ∨ (p4 ∧ p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716267307263455361902960347456 : (((((p2 → (p5 ∨ False)) → p1) ∧ ((True → True) → (((p2 ∧ True) ∨ ((p1 → p3) ∧ ((True ∨ (p3 → (p3 ∨ False))) ∧ p5))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337390696603245223021190422940 : (p1 → ((False ∨ (((((p3 ∨ True) → p5) ∧ False) ∧ (p5 → ((False ∨ (p4 ∨ ((p3 → p1) ∨ p1))) ∧ p4))) ∧ p2)) ∨ ((p5 → p2) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149688507395489349184635963057 : ((p5 ∧ (((p5 ∨ p4) ∧ (((False ∧ False) → (p3 ∧ ((p3 ∧ (True ∧ p4)) → p1))) ∧ p4)) → (p4 → p5))) ∨ ((p1 → True) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179224313142094487743749617034 : ((p4 ∧ ((p1 → True) → (((((p3 → p5) ∧ p3) → p4) ∨ p5) ∧ p2))) ∨ ((p1 ∨ p5) ∨ ((True ∧ False) ∨ (((p1 ∧ p3) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_602051234788050057954146720335 : ((((p5 ∧ (((False → p2) ∨ (True → (p1 ∨ (False ∧ (False ∨ (False ∧ ((((p2 → (False → p3)) ∨ p3) ∨ p4) ∨ p5))))))) → p4)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197815611995113569865537425468 : ((((p1 ∨ p4) → False) ∨ (p1 ∨ (p4 ∨ False))) ∨ (p3 → (True ∧ (False → (((p3 ∧ (p5 ∨ p5)) ∨ (((p5 ∧ False) ∧ True) ∨ p2)) ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173107008544736383079509910181 : ((p2 ∨ ((p1 ∨ (((p1 ∧ p3) → (p5 → p4)) ∧ (p4 ∨ (p1 ∧ p1)))) ∧ p2)) ∨ ((p1 ∧ p5) → (((p2 → True) ∧ True) → (p3 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112237054596181841607202403234 : (((p2 ∨ (p1 ∨ (((p2 ∨ ((p2 ∧ ((False → (p2 ∧ False)) ∧ p5)) ∧ ((p5 ∨ False) ∨ (p5 ∨ p2)))) → p3) ∧ True))) ∨ False) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636902720903440724545607389266 : (((((p5 ∨ (((p1 → ((p2 → p2) → True)) ∧ p2) ∨ ((p1 ∧ p3) ∧ p3))) → ((True ∨ True) ∧ (False ∧ ((p4 ∨ False) → False)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262104176603521944691518343048 : (True ∧ ((((((True ∨ (((p3 → p5) → ((False ∧ ((False → (False ∨ (p3 ∧ p4))) → p2)) ∧ p1)) ∧ p5)) → True) ∧ p2) → False) ∧ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149900198606504101051250879462 : ((p2 ∨ (p4 ∨ (p3 ∨ ((True ∨ (p4 ∧ p3)) → (((((p5 ∨ p3) → p4) ∨ (p4 ∧ p2)) ∨ p1) ∨ True))))) ∨ (False → ((p1 ∧ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136308274797510430239184222844 : ((((p1 → (True ∨ True)) ∧ p1) ∧ (p2 ∨ (((((p3 → False) → p5) ∨ p4) ∧ True) → (((p4 ∧ p5) ∨ p4) ∧ p5)))) ∨ ((False ∧ p2) → p5)) := by
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
theorem thm_5_vars_52847261621976255660747137645 : ((((p4 ∨ False) ∨ (p5 ∧ ((False ∧ (p2 ∨ p3)) → (True ∧ (p5 ∧ p1))))) → (p5 ∧ ((p2 ∨ p5) → (((p3 → p1) ∧ p1) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708023551654621555327509144218 : ((((p2 ∨ ((p5 ∨ (p5 ∨ p5)) ∧ (False ∨ False))) ∨ (True ∨ (p5 ∧ (p4 ∧ ((p3 ∧ ((p3 ∨ p2) → ((True ∨ p1) ∨ p3))) ∨ p3))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_345327523499354450249942834682 : (p3 → ((((((p1 ∧ (p4 ∨ (True ∧ (p2 ∨ p1)))) → (((p2 → p2) ∧ p5) ∨ p3)) ∧ p3) ∧ ((False ∨ True) → (p3 ∧ p4))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215985641414212850689458627879 : ((p4 ∨ (p4 ∧ (p5 ∧ p4))) ∨ ((((((p5 ∧ p3) → (((p4 ∧ p3) ∧ (p3 → False)) ∧ True)) → True) → (p5 → (p4 → p1))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157953752611491205318987200709 : ((((p1 ∨ (((p3 → True) ∧ p5) ∧ p2)) ∧ p2) ∨ ((((p5 ∧ (False ∨ False)) ∨ p3) ∧ p4) ∨ p2)) ∨ (False ∨ (p4 → (p5 → (p4 ∨ True))))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114170527467002619099465698621 : ((((((True → ((p4 → (p2 → p2)) ∧ (False ∧ True))) → p1) → ((p3 ∨ p3) ∧ False)) ∧ (p2 → False)) → ((p4 ∧ True) ∧ p2)) ∨ (False ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True → ((p4 → (p2 → p2)) ∧ (False ∧ True))) → p1) := by
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
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h14 : ((True → ((p4 → (p2 → p2)) ∧ (False ∧ True))) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- False on the left can always be used.
    apply False.elim h19
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h20 := h12 h14
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265526117129053433829557110492 : (True ∧ (False ∨ (((False → ((p3 ∨ p5) ∨ p2)) ∨ ((((p1 → ((p4 ∧ p2) ∧ (True → p4))) ∨ True) ∧ (p2 ∧ p5)) ∨ True)) → (p1 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h6.left
        let h12 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147931839616432535312018648521 : ((((p4 ∨ (p3 → (p4 ∧ (p4 ∨ p2)))) → ((False ∧ p4) ∧ (True ∧ (False ∧ (p5 → p4))))) ∧ (False → p3)) ∨ ((p3 ∨ p3) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206291385315789403130857265616 : ((p1 ∨ ((False ∧ (p3 ∧ False)) ∧ p1)) ∨ (((p2 ∧ (((p5 → p1) ∨ (p5 ∧ (p4 → p2))) ∧ (p3 ∧ (p4 ∧ (p5 → p4))))) ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40120031501627683022232740085 : (((((True → (p3 → (((p2 ∨ p4) ∨ (p4 ∧ (p1 → ((p2 ∨ ((False ∨ True) → p4)) → False)))) → p4))) → (p1 → False)) ∧ p2) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



