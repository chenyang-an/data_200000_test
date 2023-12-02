variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137778170380492990452293104312 : ((p2 ∨ ((p5 ∨ (p2 ∨ ((p3 ∧ True) ∧ p1))) ∨ (p4 ∧ (p1 ∧ ((p5 ∧ (p1 → (p1 → p1))) → (p4 ∨ True)))))) ∨ ((False ∧ p5) → p4)) := by
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
theorem thm_5_vars_325117773651686528911343710754 : (p5 ∨ ((p5 → p4) → ((((p2 ∧ (True → p2)) → p3) ∨ (p3 ∨ True)) ∧ ((((False ∧ p3) ∧ True) → True) → ((False ∧ True) ∨ (True ∨ p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48390913691244014196852142513 : (((False → ((((((p4 → ((p5 ∧ p5) → (p4 ∧ p5))) → False) ∧ False) ∨ p5) ∨ (p3 ∨ p4)) ∧ ((True ∨ p2) → p1))) → (p5 → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57427195309002317196378839340 : (((p3 ∨ (True ∧ False)) ∨ ((p1 ∧ (((True → (False ∨ p4)) ∨ ((p5 → p5) ∨ True)) ∧ True)) → (p2 ∨ (p1 → (True ∨ (p2 ∧ p1)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159000212857796928196054302817 : ((p3 ∨ (p2 → ((((p3 ∨ (False ∨ ((p4 ∧ p2) ∨ ((False ∧ p4) → p4)))) → True) → p5) ∧ p2))) ∨ (p1 → (True ∨ ((p5 ∨ p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164493061785413078517303124062 : (((((p2 ∨ (p4 → ((((p5 ∨ False) → p5) ∨ False) ∨ p2))) ∨ (p3 ∨ p5)) → False) ∧ p2) ∨ (False → ((((p2 ∧ True) ∨ False) ∨ True) ∧ False))) := by
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
theorem thm_5_vars_304677069878970266581709008207 : (p1 ∨ (((((False → True) → ((True ∧ ((((p3 ∨ p3) ∨ p3) ∧ p1) ∧ p4)) ∨ p5)) ∧ ((p1 → False) ∧ (p1 ∨ p4))) ∧ True) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218973188588861586944586376097 : ((p4 ∧ ((p2 → p2) ∨ True)) → (((p1 → (p2 ∨ ((p2 ∧ True) ∧ (True → (((((p3 ∧ True) ∧ p1) ∧ p1) ∨ p5) ∨ p1))))) → p3) ∨ p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117322434698618172717336864498 : ((False ∧ (((p3 ∧ p2) → (p5 ∨ (p4 → (p2 → p5)))) ∧ (p4 ∧ ((p2 ∧ p4) ∧ ((p5 → p3) ∧ ((p3 → p3) ∨ p3)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53662944713066364217899798987 : ((((p1 ∧ p1) ∨ (p3 ∧ (((p3 ∧ p3) ∨ p4) ∨ True))) ∧ (((p5 ∨ p2) → (p5 ∧ p5)) ∨ ((p4 → p4) → (p2 ∧ (p2 ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788845161359830794507738612309 : (((p5 ∨ (((((False → (p4 ∨ p5)) ∨ ((p1 ∨ p4) ∧ ((p4 ∨ True) → p2))) ∧ (((p4 ∧ p5) ∨ p4) ∧ p2)) ∨ p3) ∧ (p4 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54264521289167871378117749622 : ((((False ∨ (p4 ∨ (p5 ∨ p2))) → (p2 → True)) ∧ ((((p4 ∧ p2) ∧ True) → (True ∧ (p3 → (p4 ∨ (p1 → (True → False)))))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322254755759188292176777531184 : (p5 ∨ (((((False → (((p1 ∧ p3) ∧ True) ∨ p2)) ∨ ((True → p5) ∧ p5)) → ((((p1 ∨ (p1 ∧ p3)) ∧ p5) ∨ p3) ∨ p2)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262103446577381276738693843094 : (True ∧ ((((False ∨ ((((False ∨ (((True ∧ (p1 ∧ p2)) ∧ ((p2 ∧ False) ∨ p2)) ∨ (True ∨ True))) ∨ p1) ∨ p4) ∨ p3)) ∨ p3) ∧ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116064617791835989456042536885 : ((((True ∨ p4) ∧ p3) ∧ (((((p4 ∨ p4) ∧ (((p1 ∨ True) ∨ (p4 ∨ False)) ∧ (p5 → p4))) → p4) → False) ∧ (p2 ∨ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49911819138952669664685174717 : ((((((True → (p5 ∧ False)) → (((p4 → p1) ∧ True) → ((p1 → (p3 ∨ p4)) ∧ p4))) → p2) → p1) ∧ (p3 → ((p4 ∧ False) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184732456404789032666940410950 : (((((False ∨ p5) ∧ p5) ∧ p5) ∧ (((False → p3) ∧ p5) ∨ p3)) ∨ ((p4 → ((((p3 ∨ p4) ∧ ((False ∨ p1) → p5)) → p4) ∨ p2)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248334348903319800439067084636 : ((p2 ∨ p3) ∨ ((p2 ∨ (p1 → (((True ∧ (p3 → p2)) ∨ (p2 ∧ p4)) → (((p4 → (p1 → p5)) → p5) → p3)))) ∨ ((p1 → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_812482056721635865150008797206 : ((((((((p3 ∧ p3) → (True → ((p2 → p4) ∨ p1))) → ((((p5 ∧ (p1 ∧ p4)) ∧ p5) ∧ p5) ∨ p2)) → (False ∧ p5)) ∧ p2) ∧ p2) → p1) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((p3 ∧ p3) → (True → ((p2 → p4) ∨ p1))) → ((((p5 ∧ (p1 ∧ p4)) ∧ p5) ∧ p5) ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694219320311727506513994730611 : (((((((p2 ∧ p5) → True) ∧ p1) ∨ (True → ((False ∨ p5) ∧ (p3 ∨ p4)))) ∨ (p2 ∨ (True → (p5 ∨ ((p1 ∧ (p5 → True)) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77027655793411224403268870582 : ((((((p1 ∨ (p1 ∨ p1)) ∨ False) ∧ p2) → ((p1 ∧ (((p3 ∨ (p1 → p4)) → (p3 ∨ (p5 ∨ False))) ∨ p1)) ∨ (p1 → True))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ (p1 ∨ p1)) ∨ False) ∧ p2) → ((p1 ∧ (((p3 ∨ (p1 → p4)) → (p3 ∨ (p5 ∨ False))) ∨ p1)) ∨ (p1 → True))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43681683590622621101078692850 : ((((((True ∧ (((True ∧ (p2 ∧ p1)) ∨ p2) ∨ p4)) → (p4 → True)) → (((((p3 ∨ True) → p2) ∧ p2) ∧ p1) ∨ p4)) → False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148785275074740924840847346240 : (((False ∧ (p5 → (p1 → (p3 → False)))) ∨ ((((p5 ∧ ((False ∨ p4) ∧ p1)) ∨ p5) → (p5 ∧ False)) ∧ p1)) ∨ ((p4 → (p3 → p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227872439238259412264918783680 : ((p2 ∧ (p4 ∨ True)) ∨ (((p4 ∨ (p3 → (((True ∧ (((p2 ∧ p4) ∧ True) → p1)) ∨ p2) ∨ (p4 ∨ p3)))) → (p1 ∨ p1)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_65539306709480643065305343519 : ((p3 ∨ (p5 ∨ ((True → (p5 ∧ ((p2 ∨ p4) → (False → p3)))) → ((p3 ∧ (p3 ∧ p4)) ∧ ((p2 → ((True ∨ p3) → p3)) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676818105166345379056908493216 : ((((p2 ∨ ((True → ((p1 ∨ (p5 ∨ p4)) ∨ p4)) ∨ (p5 ∧ ((p5 ∨ (p4 → (p4 → p3))) → p5)))) ∧ ((p1 → p4) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135591886677933079615529193365 : ((((p5 ∧ ((((True ∧ p4) ∨ True) → (p2 ∨ p5)) → p2)) ∨ (p4 ∧ (True ∧ False))) ∨ (p4 ∧ ((p4 ∨ p4) ∨ p2))) ∨ (p2 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615443667091057268499576117241 : (((((p5 → ((p2 ∧ (p4 → (p5 ∧ p4))) → ((p1 ∨ p3) ∧ ((False → p1) → True)))) ∨ (((p4 ∧ (p3 → True)) → True) ∨ False)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57921094725863890523436662591 : (((p5 ∨ (p2 → False)) → (p5 → (p1 → (((p2 ∧ (p4 ∨ ((p5 ∧ p2) ∨ p4))) ∧ p5) ∨ ((p3 ∧ True) ∨ (p4 ∨ (True ∨ p2))))))) ∨ p5) := by
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
  case inr h5 =>
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
theorem thm_5_vars_252111651865294600499900936044 : ((p4 → p2) ∨ ((((p5 ∧ p3) → p2) ∨ p2) ∨ ((p1 ∧ (p3 ∧ (p2 → ((((False ∧ p1) ∨ p4) → (False ∨ (p4 ∧ p3))) ∧ p2)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147250191571182760297450331893 : ((((True ∧ ((((p4 ∧ (p5 ∧ True)) → ((p5 ∨ p1) ∧ (p5 ∨ p2))) → p3) → (p3 ∧ p5))) ∧ p1) ∨ p4) ∨ ((p5 → p3) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323265423351228826184418280937 : (p5 ∨ ((p2 ∨ (((((((p2 ∨ False) ∧ (False → (p4 ∧ p4))) ∧ p2) ∨ (p1 → p4)) ∧ ((p4 → p4) ∧ False)) ∧ True) ∧ False)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190886702512371031976516528653 : ((((p1 → p3) → (p5 ∧ (p5 ∨ False))) → (p1 ∧ p1)) ∨ (((True ∧ p5) ∨ p3) ∨ (False ∨ (((False ∧ ((p5 ∧ p1) ∧ p2)) → p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85104157774581360803159364441 : (((((False → (p2 → False)) → (p3 → (True → ((p5 ∧ p1) ∧ p2)))) ∨ True) → ((False ∧ ((((p1 → p1) ∧ p4) ∧ p4) ∨ True)) ∧ p4)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (p2 → False)) → (p3 → (True → ((p5 ∧ p1) ∧ p2)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216684804151955886251009549812 : ((((p3 → p3) ∨ False) ∧ True) → (((((True ∧ True) ∨ ((p2 → False) ∧ p1)) → (p3 ∨ (((p5 → p4) → p4) ∨ False))) ∨ (False → p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623964443323211063921587262390 : ((((p2 ∨ ((p1 → (((((p1 ∧ ((p3 → p1) → p1)) ∨ p4) ∧ p2) ∧ (p3 ∨ ((p4 ∨ p1) → p2))) ∧ (p2 ∧ False))) ∨ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_353882104367695001274248270553 : (p4 → (p1 → (p3 ∨ (((False ∧ p1) → p2) ∧ ((p2 ∨ (False → False)) → ((p1 ∧ (p1 → ((p3 ∨ p1) → (False ∨ False)))) → (p5 ∧ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h10 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h11
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (p3 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h18 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h19 := h9 h18
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : (p3 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23
  -- Conjunctions on the left can always be decomposed.
  let h24 := h7.left
  let h25 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h26 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h27 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47412843544130582702673528151 : (((False ∧ (((p2 ∨ False) ∨ p1) → ((p5 ∨ True) → ((p3 ∧ (p1 → (p2 ∧ ((p5 → p4) ∨ True)))) ∧ (False ∨ p4))))) ∨ (p4 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321052430126938363603366945363 : (p4 ∨ (p1 ∨ ((p2 ∧ (((False ∨ p4) ∨ p2) → ((True ∧ p1) ∨ (p2 ∧ (p5 ∨ ((p4 ∨ (p3 ∧ (False ∨ (False ∧ p4)))) → p5)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651872153872366761449658406682 : (((((p3 ∨ p1) → (p4 ∨ ((((False ∨ p2) → p2) ∧ ((True ∧ (p5 → True)) ∧ (p4 ∧ p5))) → (p5 → (False ∨ p5))))) ∧ (p4 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138154730312336889290588624326 : ((p1 → (((((p2 ∨ (False ∧ True)) ∧ p5) → p3) → ((p1 ∨ (((p2 ∨ (p4 → p1)) → p1) → p1)) ∨ False)) → p4)) ∨ ((False ∧ False) → p3)) := by
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
theorem thm_5_vars_64092171170265673581303430481 : ((False ∨ (((p2 ∨ (p1 ∧ p3)) → (((False ∨ (p5 ∧ p1)) ∨ p3) ∧ True)) → ((((p4 → False) ∨ p4) ∧ (p4 ∧ p4)) ∨ (p5 → True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_311060026111149148520961528122 : (p2 ∨ ((False ∨ False) ∨ (True ∧ ((True ∧ ((p3 ∨ (p2 ∨ (p2 ∧ False))) ∨ p4)) ∨ (p1 → ((p4 ∨ ((p3 → p3) → (True ∨ p1))) ∨ False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60308754889331173066231810511 : (((p1 → p3) → ((((p3 → p5) ∧ p2) ∧ (p4 → p5)) ∨ (((p5 → ((False ∨ p4) → (((p3 ∧ p2) → True) → False))) → p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733386663437633488070100160666 : ((((p4 ∧ False) ∧ (((p5 ∨ (p3 ∧ (((True ∧ (p4 → ((((p3 → p1) → p4) → p5) ∧ True))) ∧ True) → p2))) ∧ (p2 → p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623386069089962945934681403358 : ((((False ∨ ((p3 ∨ ((True ∨ p5) → ((True ∧ p4) ∧ (p1 ∧ (((((p3 ∨ (p1 → False)) ∧ p5) ∨ p1) ∧ True) ∨ p5))))) ∧ p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329433135176924438816688490448 : (True → ((False ∨ True) ∧ (((p4 ∨ (((False ∧ True) ∨ p4) → (p4 ∨ p1))) ∧ True) ∧ (((p2 ∨ (p4 ∨ (p4 ∧ p2))) ∧ p5) ∨ (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148831452844167942333377967705 : (((((p3 ∧ p4) → True) ∧ False) ∧ (p3 ∨ (p4 → (False ∧ ((p4 → p2) → (((True ∧ p2) → True) → False)))))) ∨ (((False ∨ p4) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602724139784323588802713263524 : ((((False ∨ ((p5 → False) ∨ ((False ∧ (p1 ∨ p3)) ∨ (((((True → p1) → p4) → p2) ∧ (p1 ∧ (p2 ∨ (p4 → p5)))) ∨ p3)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350934754387089737507393175565 : (p4 → (((p4 ∨ ((p1 ∧ (p3 ∨ p3)) ∨ ((((p4 → (p4 ∧ p3)) → p5) ∨ (((True ∧ p1) ∧ p1) ∧ p2)) ∨ p3))) → p1) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_119517970434597913570880180541 : ((p5 → (((p2 ∨ ((((((p5 ∧ (p5 ∨ (p4 ∨ p3))) → p2) ∨ True) ∨ (True ∨ p1)) ∨ (p3 ∧ p3)) → p1)) ∨ p1) ∨ p5)) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659168122344408382158215425005 : ((((p3 → ((p1 ∧ False) ∨ ((True → ((p5 ∧ False) → (((p4 → (p1 ∧ p1)) ∧ (p4 ∧ p5)) ∧ p1))) → (p5 ∧ p2)))) ∨ (True ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_52200655784648560217592131610 : ((((p1 ∧ (p2 ∨ True)) → (p5 ∨ (((p1 ∧ p1) → True) ∨ (p3 → (p1 ∧ False))))) → ((p5 → (True ∧ p5)) ∧ ((p3 ∧ p4) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317685158467432380659067936406 : (p4 ∨ (((p1 ∨ (((p4 ∨ (False ∧ (p2 ∧ (((p5 → (False ∨ True)) → False) → ((p4 → p4) ∧ p3))))) → (p4 ∨ True)) ∨ False)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668908885041731084892756686351 : (((((p1 ∧ ((p1 → p4) ∧ ((((p2 ∨ p5) ∧ p3) → ((True ∧ p4) ∨ (True ∨ p5))) → (p1 → p1)))) ∨ False) ∨ ((p2 ∨ p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214516875027585144829577841915 : (((p4 ∧ p2) ∧ (p1 ∨ p3)) ∨ ((((((p4 ∧ False) ∧ (p3 ∨ p1)) → p2) ∧ p3) → (((p2 → p5) ∧ p4) ∨ True)) ∨ (p1 ∧ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_58998592648199320056967886628 : (((p3 ∧ p1) ∨ ((p4 ∨ ((p5 ∨ (p5 ∧ True)) ∧ True)) ∨ (False → (((p4 → (p5 ∨ p2)) ∧ p5) → ((p3 ∨ (p1 ∨ p5)) ∧ p1))))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103084928483220993823674175804 : ((((p4 ∧ (p2 ∨ (True → p1))) → ((False ∧ False) ∧ (True ∧ ((p4 ∨ (False ∧ p4)) ∧ ((True ∨ p4) ∨ (p4 ∨ True)))))) ∨ True) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37769888905462506577875320370 : ((((((True → p1) ∧ p3) → (((p1 ∧ (False ∧ p3)) → ((p5 ∧ p5) ∧ (p1 → False))) → ((p2 ∨ True) ∧ (True ∧ p1)))) → p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711878213973487231279488535425 : (((((False ∨ ((p1 ∨ p1) ∨ True)) ∧ p2) ∨ ((((False → (True ∨ ((p3 ∧ p1) ∨ p3))) → p5) ∧ (p1 → True)) ∨ ((False ∧ p1) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442324728118749859324419302055 : ((((((p5 → ((p4 → True) → False)) ∨ ((p3 ∨ p1) → ((p4 ∨ ((p3 ∨ p4) → (p4 ∨ True))) → p2))) ∨ True) ∨ ((False ∨ p4) → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126966541381367750551394078560 : ((True ∨ (((p5 ∨ (p4 → p1)) ∨ p2) → ((False ∨ (p2 → (False ∨ ((p5 ∧ p2) → False)))) → (p1 ∧ (False ∨ (p2 → False)))))) → (p1 → p1)) := by
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
theorem thm_5_vars_660074353199059007721944431944 : ((((((((p1 → (p1 ∧ False)) → ((((True → (p5 ∧ p1)) ∨ p3) ∨ p4) → p3)) ∧ (p5 ∨ p2)) → (True ∧ p3)) ∨ p3) → (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57510803172385065172949259433 : (((p3 → (p4 ∨ p2)) ∨ ((p3 ∧ (p4 → p3)) ∨ ((p1 ∨ (False → False)) ∨ ((((p3 ∨ p1) → (p2 ∨ p1)) ∨ (False ∧ False)) ∨ p1)))) ∨ p4) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204659476068404075179391555715 : (((p4 ∧ (p1 ∧ (p3 ∨ p5))) ∨ p5) ∨ (True ∨ (((p3 → p5) ∧ (p3 → ((p5 ∨ ((True ∧ p1) → p5)) → (p1 ∧ False)))) ∨ (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84699005887244268686058939840 : (((((p1 → (p2 ∨ (((p3 ∨ p4) ∨ p5) → (False → p3)))) → True) → p2) ∧ ((p5 → (p4 → p4)) ∨ (((p5 → p5) ∨ False) ∨ p4))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 → (p2 ∨ (((p3 ∨ p4) ∨ p5) → (False → p3)))) → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h11 : ((p1 → (p2 ∨ (((p3 ∨ p4) ∨ p5) → (False → p3)))) → True) := by
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h11
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : ((p1 → (p2 ∨ (((p3 ∨ p4) ∨ p5) → (False → p3)))) → True) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683272817210866894233947745958 : ((((p1 ∨ (p1 ∨ ((p1 ∧ (p3 ∧ True)) ∨ (p1 → ((p3 → (p5 ∨ False)) ∨ (True ∨ p1)))))) ∧ ((False ∧ (False ∨ (p1 → False))) → p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112408857602278169882337934096 : ((((p3 ∧ (((p4 ∨ True) ∧ (p1 → (p4 → (p5 ∨ (False → (p4 ∨ ((True ∨ p3) ∧ p2))))))) ∧ (p5 → p5))) ∧ True) → False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740350786863480564846628691193 : ((((p1 ∨ p2) ∨ ((((False → (p5 ∨ (False ∨ (p3 ∧ p2)))) → p5) ∨ (p5 ∧ ((((p5 ∨ p3) ∨ False) ∧ p3) → (p1 → p4)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196491831975633562881169065958 : ((p1 → (False → ((False ∨ (False → p2)) → p4))) ∧ (p2 ∨ ((((p4 ∨ p3) ∧ p2) ∧ ((p1 → (((p5 → p4) → p1) ∨ p4)) ∨ False)) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114414575441425265398842278122 : ((((p1 ∧ True) ∧ (((p5 ∧ p5) ∧ (p2 → (p2 → (((p1 ∧ p4) ∧ p4) → p1)))) → p4)) ∨ (p1 ∨ (p2 ∧ (True → False)))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682577539706028317481183683749 : ((((((((p5 → True) → (True ∨ p5)) ∨ p2) ∨ p2) ∧ (p2 → ((p4 ∧ (False ∧ p1)) ∨ p2))) ∧ (((p3 → p2) ∧ p4) ∨ (p3 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255014612211335324086720610783 : ((p4 ∧ p1) → ((p2 ∨ (p3 ∧ ((p3 ∨ (p2 ∨ (p4 → p1))) → (p2 ∧ ((p4 ∧ ((p2 ∧ p2) ∧ True)) → p2))))) ∨ ((p5 → p1) ∨ True))) := by
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
theorem thm_5_vars_239998812591170592296331607011 : ((p4 ∨ True) ∧ ((((((p3 ∨ (p5 ∧ False)) → (p4 ∨ p5)) ∨ (p1 ∨ p3)) → (p1 → ((True ∧ p3) ∧ p5))) ∧ ((p4 ∨ p4) ∧ p5)) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307499516330191043779931491288 : (p1 ∨ (True → ((((p1 → ((p1 ∨ (True ∧ False)) ∨ (p5 ∧ p1))) ∧ (True ∧ (p1 ∨ ((False ∧ True) ∧ p4)))) ∧ p4) ∨ (p1 ∨ (False → p2))))) := by
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
theorem thm_5_vars_213403974698267838031167052746 : (((p1 ∨ (p2 ∨ p4)) ∧ p5) ∨ (p1 → ((False ∨ p3) ∨ ((False ∧ True) → (False → (((p4 → (False ∧ (True ∨ (p4 → p5)))) ∨ False) ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63266812808448075520969130303 : ((p5 ∧ ((((p5 ∧ p4) ∧ p3) ∨ (True → p3)) ∨ (True → ((p5 → ((p1 ∨ p1) → (p4 → (((p5 → p4) ∧ p5) ∨ p2)))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155308525463903018493340076800 : (((p3 ∧ ((p1 ∨ (False → True)) → False)) ∨ (p3 → ((((p3 ∨ (True → False)) ∨ p4) → p4) → p4))) ∧ ((p1 → (p5 → (False → p4))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (True → False)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186075057657975979936934327839 : (((((p3 → (False ∨ (p1 → (False → p3)))) ∨ p1) → p3) ∨ p1) → (p1 → ((p5 ∧ ((((p5 → (p1 → p5)) ∧ p1) → True) → False)) ∨ p1))) := by
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
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155288849302627410039804198841 : ((((((True → p2) ∧ True) → p4) ∧ p5) ∨ (p5 → ((False ∨ (False → False)) ∨ ((p3 ∨ False) ∨ p3)))) ∧ ((p4 → p1) → ((True → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324414228517978994763541061351 : (p5 ∨ ((p1 ∧ ((True ∨ (p4 ∧ p4)) ∨ True)) → ((((True ∨ ((p1 ∨ (p2 ∧ (p1 ∧ False))) → p3)) ∨ p1) ∧ (p5 ∨ p2)) ∨ (p1 ∨ False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165246321458773417960130083266 : (((p3 ∨ ((((False → (p5 ∨ ((p2 ∨ p5) → p4))) ∧ p5) → p3) ∧ p2)) ∨ (p2 ∧ True)) ∨ (p2 → ((True ∨ p1) ∧ (p5 → (True → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177666109397363483222070179480 : ((((p4 → ((True → (p3 ∨ p4)) ∧ (True → (p2 ∨ False)))) ∨ p1) ∧ False) ∨ ((p4 ∨ True) ∨ (p4 ∧ ((p1 → (p3 → (True ∧ p3))) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200096233469781211918447712869 : ((((p2 ∨ p4) → p5) ∧ ((p1 ∧ True) ∨ p3)) → ((p1 ∨ ((p2 ∨ (p3 → (((p2 ∨ p4) ∨ p2) ∨ (p5 ∨ p4)))) ∨ False)) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342899225536900137008106941417 : (p2 → (((p2 ∨ (p5 ∨ p1)) → (p2 ∧ False)) → ((p3 ∧ p2) → ((True ∨ (p2 ∨ (p3 → (((p1 → (p3 ∧ p1)) → p3) → p1)))) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p2 ∨ (p5 ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p2 ∨ (p5 ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : (p2 ∨ (p5 ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- We need to get the right conjuct of h22 based on <expert-advice>.
      let h23 := h22.right
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307195833028832498921845483386 : (p1 ∨ (p1 ∨ (((((p5 ∨ p4) ∨ ((((p3 ∧ (p1 ∨ ((False ∧ p5) ∧ p3))) ∨ p2) ∨ p2) ∨ p2)) ∧ p5) ∧ p4) ∨ (False → (p1 → p3))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_770026787092675083434539389257 : (((p5 ∧ (p2 → (p3 ∧ (((p4 → ((p2 ∨ (((p3 → ((p3 ∧ p2) ∧ p4)) → (p4 ∨ p2)) ∨ p4)) ∨ (p2 ∧ p1))) ∨ p2) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167882858591873893094608262696 : (((p4 ∧ (((((True ∧ p2) → p4) → p3) → p4) → p4)) → ((p1 → (p4 → True)) ∨ p2)) → (((p3 ∧ (False ∧ (p4 → False))) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75765336095736356138213799762 : (((((((p3 ∧ ((p3 ∧ p4) ∨ p3)) ∨ p1) ∨ (p3 ∨ (p2 ∧ p4))) ∨ (p2 → (True ∨ (p3 → ((p2 ∨ False) ∨ False))))) ∨ False) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p3 ∧ ((p3 ∧ p4) ∨ p3)) ∨ p1) ∨ (p3 ∨ (p2 ∧ p4))) ∨ (p2 → (True ∨ (p3 → ((p2 ∨ False) ∨ False))))) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213093950038962926526929628698 : ((((True ∨ False) ∧ True) ∧ p5) ∨ (((False ∨ True) → p1) → (p2 ∨ (True ∧ (((((p3 ∨ False) ∧ p2) → p3) → p2) ∨ ((p2 ∨ p5) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221721870384695635490565661825 : (((False ∧ p2) → False) ∧ ((p1 → p2) → (((((p5 ∧ p3) ∧ p5) ∧ p5) → (((p4 → (True ∨ p2)) → p2) ∨ p3)) ∧ (True ∨ (p2 → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781572419412126806873083345762 : (((p2 ∨ (False ∨ ((p1 ∧ p1) → (((False → (((p4 ∨ True) → p5) ∧ (p2 → p3))) ∧ p3) → ((p5 → p5) ∧ (p4 ∨ (p4 ∨ True))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115981783618660059839603103532 : ((((True ∧ (False ∧ p1)) ∨ p2) → (p1 → ((p2 ∧ (p2 → (p3 ∧ (((((p4 → p5) ∨ p5) ∧ p5) ∨ p1) ∧ False)))) → False))) ∨ (p5 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232263007035113192242540888174 : (((p2 → False) → p4) → (p3 → (((True → (((True → (((False → (True ∨ False)) → p2) ∨ p3)) ∧ ((True → False) ∧ p2)) ∨ True)) ∨ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346637531209982277212521604051 : (p3 → ((False ∨ (p4 ∨ ((((((p5 ∧ p3) → p5) ∨ p4) ∨ ((False ∨ p4) ∧ p5)) → False) ∧ ((p2 ∨ p2) ∨ p4)))) ∨ (p3 → (p1 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159429984002275658797607765185 : ((((((((True ∨ ((p5 ∨ p4) → (False ∧ p3))) → p5) ∧ p2) ∧ True) ∨ True) → (p2 ∧ p4)) ∧ True) → ((p2 ∨ p4) ∧ (True ∧ (p1 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∨ ((p5 ∨ p4) → (False ∧ p3))) → p5) ∧ p2) ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221709975334019605351768316807 : (((False ∧ False) → True) ∧ (p5 ∨ (p5 → (p3 ∨ (p5 ∧ ((((False ∨ p3) ∨ ((True → (False ∨ True)) ∧ (p1 ∨ (p5 → p3)))) ∨ p5) ∨ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258810939155105994339636430355 : ((True → False) → (p5 ∨ ((((p5 ∧ ((p2 → False) ∨ (False ∧ p4))) → (True → (p2 ∨ (p4 ∧ False)))) ∨ ((p3 ∧ (p5 → True)) ∨ False)) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193224799682069501614264414236 : ((((p5 ∨ p1) ∧ p3) ∧ (((p4 ∨ True) → False) ∧ True)) → (((p3 → (False ∧ False)) ∨ ((True → False) ∧ (p2 ∧ (p1 ∧ (p5 → p2))))) ∧ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h14 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h15 := h12 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710143664869522770320157168739 : ((((((True ∧ (p1 ∨ p1)) ∨ p4) ∨ p1) ∧ ((((p2 ∧ p2) → p1) ∨ ((p1 → False) ∨ (p2 ∧ ((True ∧ p3) ∨ p5)))) ∧ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



