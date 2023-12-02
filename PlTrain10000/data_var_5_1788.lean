variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611996350522737745116682414417 : ((((((p3 ∨ ((p3 ∧ ((((p4 → p4) ∨ ((p4 → True) → p3)) → p2) ∨ ((True → True) ∨ True))) ∨ p3)) ∨ p5) ∧ (p5 ∧ p3)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_151471569929503663668661044659 : ((((True ∧ (((p3 → p3) ∨ (p5 ∧ ((p1 ∧ (p3 → (p3 ∧ False))) ∨ p2))) ∨ True)) → p5) ∨ (p3 ∧ p4)) → ((p3 ∧ True) ∨ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∧ (((p3 → p3) ∨ (p5 ∧ ((p1 ∧ (p3 → (p3 ∧ False))) ∨ p2))) ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137528148404631288261265954959 : ((p5 ∧ (p2 ∧ ((True ∨ ((((True ∨ True) → (p5 ∧ p5)) ∨ p2) → (p1 ∨ p2))) → (((p4 ∧ p5) ∨ p4) → p5)))) ∨ (p3 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654113087582043164949243050366 : ((((((((p2 → (p5 → ((p2 ∨ ((p4 → False) → (((p1 ∨ True) ∨ p4) → p3))) ∨ p3))) → True) → p1) ∧ p2) ∨ True) ∨ (False ∧ False)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_52264337912617254780653677052 : (((p5 ∨ (((p2 ∧ (((p2 ∨ p3) ∧ True) ∨ p2)) ∧ ((p4 ∧ p2) → p3)) ∨ p1)) → (((p3 ∨ p2) ∨ True) ∨ ((p2 → p3) → p2))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
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
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38082044909326831660516291806 : (((((p4 → p4) → (((p2 → (p5 ∧ (p3 ∨ p4))) ∨ False) ∨ (((True ∧ ((True ∧ p5) ∧ True)) ∨ p2) ∧ p1))) → (False ∧ p1)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256481147825466463533020785980 : ((False ∨ p4) → (((p4 ∨ (True ∧ (p1 ∨ p5))) ∧ (p1 → False)) ∨ (((p3 ∨ (True ∧ (False ∧ ((p4 ∨ True) ∧ p2)))) ∧ p5) ∨ (True ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134405376716905047061115329951 : (((p1 → (((((p2 → (p3 ∨ (True ∧ (p5 ∨ ((True ∧ p1) → True))))) ∨ p3) → p4) ∧ (p2 ∨ p4)) ∨ p5)) ∨ p3) ∨ (True ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356163328544553674944789829275 : (p5 → (((p1 → False) ∨ (((p2 → (((((p4 → p2) → p2) → True) ∨ p2) → p1)) ∨ p5) → p4)) ∨ (p1 → ((p1 ∨ (p3 ∧ True)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350170251738384661650010943906 : (p4 → (((((p1 → (p4 ∧ p3)) ∧ p4) → False) ∨ (p1 ∧ (False → ((((p3 ∧ p2) ∨ p5) ∧ ((p1 ∧ p5) ∨ (True ∨ p1))) → p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328540300878838195949498872758 : (True → (((((p2 ∧ p3) ∨ ((p5 ∧ p4) ∨ (p3 ∨ (p1 ∧ (False → p3))))) → False) ∧ p3) → ((p5 → ((p2 → False) ∨ p3)) → (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ p3) ∨ ((p5 ∧ p4) ∨ (p3 ∨ (p1 ∧ (False → p3))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609870763121927073827466796684 : (((((p2 → ((((False ∨ ((True ∧ p1) ∨ p4)) ∧ (p2 ∧ (((p2 ∨ p5) ∨ p1) ∨ True))) ∨ (p3 ∨ (True → p3))) ∧ p5)) ∨ p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_660850919235917881448620490442 : (((((p3 ∧ (p1 ∨ (p3 → (True → ((p4 → ((False → (p5 ∨ (p3 → (p3 → p3)))) ∨ p3)) → (False → True)))))) → False) → (p1 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309780078069894409967711416670 : (p2 ∨ (((p1 ∧ (((p1 ∧ (((p5 → p1) → (p2 → False)) ∧ p2)) ∧ (True ∨ (p5 ∧ p2))) ∨ True)) ∧ True) ∨ (True ∨ (p5 ∧ (False ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190180448080854155878349793162 : (((p5 ∧ (((False → p4) ∨ p2) → (p4 → p3))) ∧ True) ∨ (p2 → ((p2 → ((p5 → (((p4 ∧ p4) ∧ (p3 ∨ p2)) ∨ p5)) → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194011982673615765076313042810 : ((p4 ∨ (((False ∧ True) ∧ (p5 ∧ p4)) → (p1 → p1))) → ((((p3 ∧ (p3 ∨ True)) ∨ p2) ∨ p4) ∨ ((((p3 → p3) ∨ p5) → False) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 → p3) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172553612560588667358385439860 : ((((p1 ∨ True) → False) ∨ (True → ((p2 → (p2 ∧ (p3 ∨ (p5 → p5)))) → p5))) ∨ ((False ∧ True) → (True → (False → (p5 ∧ (p4 → p1)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611059479362139059741626866428 : ((((((((p4 ∧ p4) → p4) ∧ True) ∧ ((((p1 ∨ p1) → ((p2 → (True ∨ p1)) → p4)) → (p5 ∨ p1)) → (p4 ∧ p3))) → p3) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_41638912824387658791151162468 : ((((p4 → (True ∧ (True ∨ (p4 → (p2 ∨ p4))))) → ((p1 ∨ ((p3 ∨ (p1 ∧ (p1 → False))) ∨ p2)) ∧ ((p4 ∨ p5) → p3))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200354968624600379375493878618 : (((True → p4) ∧ ((p5 ∧ p1) → (False → p2))) → (False ∨ ((p1 → (((p1 → True) ∨ (True → ((p5 ∧ True) → False))) ∧ (p2 ∧ p3))) ∨ True))) := by
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
theorem thm_5_vars_614577121350696728522936044974 : ((((((p3 ∨ p5) ∧ ((p2 ∧ ((True ∨ p4) ∨ (((p5 ∧ False) ∨ p1) ∧ (p1 ∧ p4)))) ∨ False)) ∧ ((False → False) ∧ (p3 ∧ True))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173200188650589646919019517440 : ((p5 ∨ ((p5 ∨ ((((p1 → p3) ∧ p3) → ((p4 → p3) ∨ p2)) → p4)) ∨ True)) ∨ ((p1 → (p3 ∨ (((p2 → p5) ∨ p3) → p4))) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47800691213286949870970083788 : (((((p1 ∧ (p3 ∨ ((p4 → True) ∨ ((p5 → ((p1 ∨ p5) → False)) → ((p5 → (True ∧ p4)) ∨ p5))))) → p5) → True) → (False ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643587359908449803111221863928 : ((((p4 ∧ (p4 ∧ (True → (((True → (p1 ∨ (p2 ∧ p4))) ∨ (p5 ∨ True)) ∧ ((p5 ∧ p5) ∧ (p5 ∨ (True ∧ (p1 ∧ p2)))))))) → p5) ∨ False) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
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
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715789016334564747038959872587 : ((((((p1 ∧ p2) → False) ∨ False) ∧ (((False ∧ (p5 ∨ (p2 ∧ (p2 ∨ p4)))) ∨ True) ∨ (((p3 ∧ False) → (p2 → False)) ∧ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340891134990876193542188973313 : (p2 → ((((p5 → p2) → ((((((p4 ∨ True) ∨ p2) ∧ p5) ∧ p2) ∨ p3) ∧ p4)) → (True ∧ ((((p1 ∧ p2) → p3) ∧ p5) → p4))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p5 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133543046032183766672160901841 : ((((p2 ∧ (((p3 ∨ p1) → ((((p1 ∨ (((True ∨ p1) ∧ p4) → True)) → p2) → p2) ∧ False)) → p5)) ∧ True) ∧ p4) ∨ (p2 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351278883974479037370550051263 : (p4 → (((((p2 ∨ ((p2 ∨ (p2 ∧ (False → True))) → (p3 → ((False ∧ (p2 → p4)) ∧ p4)))) ∨ p5) → p1) ∨ False) → ((True → p2) → p2))) := by
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
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149268829331897307480693426604 : (((True → p2) ∨ (((((True → (p5 ∧ (p4 ∧ (True ∨ p4)))) ∧ (p4 → (p5 → p2))) ∧ p2) → p5) ∨ p2)) ∨ (p2 ∨ (p5 ∨ (p1 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197436224640964755910558430224 : ((((True ∧ (p3 ∨ p2)) ∧ p4) ∧ (p3 → p2)) ∨ ((((True ∧ (((True ∨ p5) ∧ (p2 ∨ p5)) → ((p2 → p4) → p5))) ∨ p5) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228873783005251075133643613347 : ((p4 ∨ (False ∧ True)) ∨ (p1 ∨ ((p5 → p1) → (((p5 ∨ ((p3 → p1) ∨ p3)) → p2) ∨ ((p2 → (p4 → (p3 → (p4 → p4)))) ∨ p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732970411366807750139210316543 : ((((p2 ∧ p3) ∧ (((p5 ∨ (p1 ∨ (True → p1))) ∨ p4) ∨ ((p4 ∨ (p3 → (((False ∨ False) ∧ p3) ∧ (p3 ∧ (p1 ∧ p1))))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68167767808631483904253892620 : ((p3 → ((True → (((p2 ∧ ((p5 → (((p4 → p5) ∧ (False ∨ True)) ∨ p1)) ∧ (p1 ∧ (p5 ∧ False)))) ∨ p3) ∧ (p1 ∨ p3))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260932871357459540746569884795 : ((p4 → False) → (False ∨ (((p3 ∧ True) ∨ ((p2 → p3) ∨ p3)) ∨ (True ∨ ((True ∨ p1) ∨ ((True → (((True ∨ True) ∨ p1) ∧ p5)) ∨ False)))))) := by
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
theorem thm_5_vars_595314999053856063843540555323 : (((((((((p5 → (True ∨ p4)) ∨ p4) ∨ p4) → p2) → (p3 ∨ False)) ∧ (((p3 ∨ p2) ∨ ((p3 ∧ (p4 ∨ p5)) ∨ p3)) ∨ True)) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37364913727367088264881784991 : ((((((p5 → p3) ∨ (((p5 → False) → (((((False → (False → p3)) ∨ p5) → p5) → (p3 → p5)) ∧ p3)) ∧ p4)) ∨ p5) ∨ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204814351038400162673449950166 : (((((False ∧ p3) → p1) ∨ True) → p3) ∨ ((p3 → (False → p3)) ∨ ((True → p2) → (p4 ∧ ((p5 ∧ (p1 ∧ ((p2 ∨ p5) ∨ p4))) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631575408525399435597904286526 : ((((((p1 ∧ ((False → (((p4 ∧ p4) ∨ p4) ∧ (p5 → p3))) ∨ ((False ∨ (p1 ∧ False)) ∨ p1))) → (False ∧ (p3 ∨ p5))) → p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49375329606757531670818325689 : (((p5 → (((True ∨ (True → (p3 ∧ p1))) ∨ (p4 ∧ (p5 → (p5 ∧ True)))) → ((False ∨ (p5 ∧ p3)) ∧ p2))) ∨ ((p4 ∧ False) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321071208788871236667918746149 : (p4 ∨ (p1 ∨ (((((((False ∨ p3) ∧ True) → p1) → ((p5 ∨ p3) ∧ p3)) ∨ p3) → False) → (p4 → ((((p1 → p5) → p2) ∧ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151770610634146051636831249255 : ((((((p4 → True) ∨ p2) → False) ∧ (p2 → ((p3 ∧ True) → (p3 ∧ (False → False))))) → ((p1 ∧ False) ∨ p1)) → ((p1 → (p4 ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119455793219615771270511749497 : ((p4 → ((p5 ∨ ((False ∧ p2) ∧ p5)) ∨ ((p1 ∨ (p5 ∧ p4)) → ((((False ∧ False) ∨ (p2 ∨ p1)) ∧ True) → (False ∧ p5))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112048934718222143122226340826 : ((((p2 ∨ (True ∧ p4)) → ((((p2 ∧ p1) ∨ ((((False ∧ p3) → p2) ∨ p2) ∧ p4)) ∨ (p1 ∧ p4)) ∨ (p1 ∧ p1))) ∨ p2) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201118073193372042628093101600 : ((True → (p1 ∧ (((p5 ∧ p1) → p1) ∧ p4))) → (((True ∨ p5) ∨ p4) → ((((True ∧ p2) ∨ p3) → ((p3 ∧ (p1 ∨ p5)) → p4)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591104964545728554817382646320 : (((((((p3 ∧ p3) ∨ ((((p3 ∧ (False ∧ ((False ∨ p1) ∧ (p2 ∧ (p1 ∧ p2))))) → p2) → p5) ∨ p4)) ∧ p4) ∧ (True → p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318608374202954810358799347268 : (p4 ∨ ((((p1 ∨ (False ∨ False)) ∨ True) ∧ (((p3 ∧ ((((p5 → p3) → p1) ∨ False) ∨ p2)) ∨ p5) ∧ (p3 ∧ (p2 ∧ p5)))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8749637940411212096230542207 : ((((True ∧ ((False ∧ (p3 ∧ ((False ∧ (p5 ∨ (False ∨ (((False ∨ p2) ∧ False) → False)))) ∧ p5))) ∨ True)) ∧ ((True ∧ True) ∨ False)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_728349483163800596596650014723 : ((((p1 → (p1 ∧ p5)) ∨ ((p5 → ((((p4 ∧ (False ∧ p3)) → (p1 ∧ (True → (False ∨ False)))) → (p5 ∧ False)) ∧ p4)) ∧ (p1 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171420452025042248544500131157 : ((((False ∧ p4) ∧ (((p2 → ((p4 → (p1 ∧ p1)) → False)) ∨ True) ∨ p2)) ∧ False) ∨ (False → ((True ∧ ((True ∨ True) → p3)) ∨ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299290450621163328041525213641 : (False ∨ (((p1 → (((p4 ∧ (True ∨ True)) → ((p3 → p4) ∨ p3)) ∧ p5)) ∨ ((p5 ∨ ((p2 → (p2 ∧ p3)) ∨ (p4 ∨ False))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53445973447557061844710113776 : ((((p3 → (p2 ∨ False)) ∨ (p1 ∨ ((False ∨ p5) → (p5 ∨ p5)))) → ((p5 ∧ True) ∨ ((False ∧ p2) ∨ ((False ∨ p5) ∨ (p3 → True))))) ∨ p3) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59170247009325000859003826517 : (((False ∨ p4) ∨ ((p1 ∨ ((p1 ∧ p1) → (((((((True → False) ∧ (p3 → p5)) ∨ p2) ∨ p2) → p5) ∨ (p1 ∧ False)) ∨ p2))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192348187775611812392285045244 : (((p5 ∨ ((p4 ∨ p1) ∧ (p4 → (p2 ∨ True)))) ∧ p5) → ((((p1 ∨ p2) ∧ (p4 ∧ p5)) ∨ p4) ∨ ((p4 ∨ p5) ∨ ((p1 → p5) ∨ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232174000134247352612697924499 : (((False → True) → True) → (((p5 → p5) → (p3 ∨ ((p3 ∧ ((p1 ∨ (p4 ∨ (p5 ∨ True))) ∨ (p3 ∨ False))) → ((p2 ∨ p4) ∨ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h4
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248309409417012352711169979652 : ((p2 ∨ p2) ∨ (p3 → (p5 ∨ ((p3 → ((p5 → p4) → (p2 ∨ (((p4 → p3) → p1) → (((True → p4) ∨ p1) ∨ True))))) ∨ (p2 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223981238776318177368157915440 : ((p4 ∨ (p5 ∨ True)) ∧ (((p3 ∧ ((p1 → ((True ∧ (True → ((False ∨ p3) → (p2 ∨ (p3 → p4))))) → p1)) ∨ p4)) → p5) ∨ (p2 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809378114492103507790821553997 : (((p5 → ((p2 → (p4 ∨ ((p2 ∧ (p1 ∨ (((p5 → p5) → ((p2 ∨ p5) ∧ (True → p1))) ∧ False))) ∨ ((p1 → p4) ∧ p2)))) ∨ p5)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_66447847625615403127276802664 : ((True → ((((((p4 ∧ (((p5 ∨ ((False ∨ False) → p4)) → True) → p2)) ∧ p5) ∨ p5) ∧ True) ∨ (p1 → (p1 ∧ (False → p2)))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167123224923451050952517078870 : ((((((p4 → p5) ∨ p5) ∧ (True → (p4 ∧ p1))) ∧ (((p4 ∧ p5) ∧ p4) ∨ p5)) ∨ p2) → (p1 → ((((False → True) ∨ True) ∧ p1) → p1))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h14.left
          let h17 := h14.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h21.left
          let h24 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h29.left
      let h32 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h39 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h40 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- Conjunctions on the left can always be decomposed.
          let h44 := h42.left
          let h45 := h42.right
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h46 =>
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h47 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200079149189270310906800753667 : ((((p2 ∧ True) ∨ p1) ∧ ((p5 → p2) ∧ p4)) → (p2 → (((p2 ∧ p5) ∨ (True ∧ (((((p5 ∨ p2) ∧ p3) → p5) ∨ True) ∨ p3))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164750096577917811099622038313 : (((((((p3 ∨ p4) ∧ (p4 ∨ p1)) ∧ (True → p1)) ∧ (True → p5)) → (p1 ∨ p1)) ∨ p5) ∨ ((p3 ∧ (p5 ∨ ((p3 ∧ p3) ∨ p1))) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h11 := h5 h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134832687182776430771242445329 : (((p2 ∨ (((True → p3) ∧ (p2 ∧ (((p4 → False) → (False → p4)) ∧ (False ∨ p5)))) → (False ∨ (p2 ∨ p5)))) → p1) ∨ ((p4 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157906449304839294892933730459 : (((((False ∧ (p5 ∨ (p5 → p2))) ∨ p3) → (False → False)) → ((p4 ∧ p3) ∧ (p3 ∧ (False → p1)))) ∨ (((False ∨ p3) ∨ p4) → (p4 ∨ p3))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60063364295253316204109793779 : (((p2 ∨ p1) → (True → ((((False ∧ p3) → (False → p4)) → ((False ∨ (p1 ∧ (p3 ∨ p3))) ∧ (p4 ∧ ((True → False) ∨ True)))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208307621718983531779681834341 : (((p5 ∨ p3) ∧ (True → (p3 ∧ p2))) → (p4 ∨ ((((False → ((p5 → p3) → (((p4 ∨ p5) → (True → False)) ∧ p5))) → p1) ∧ p2) ∨ True))) := by
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
theorem thm_5_vars_150455960718412437586429903687 : (((((p2 → p1) ∨ ((p2 → ((p3 ∨ p1) → (p5 → (p2 → ((True → p2) ∧ p4))))) → p4)) → False) ∧ p4) → ((True ∨ p2) ∧ (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((p2 → p1) ∨ ((p2 → ((p3 ∨ p1) → (p5 → (p2 → ((True → p2) ∧ p4))))) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h7
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205934380231923815770607263975 : ((False ∧ ((p1 ∨ False) ∧ (p1 ∨ p1))) ∨ ((p4 ∨ ((((p1 → ((p2 → (p1 → p1)) ∧ (p1 ∨ p4))) ∨ False) → p5) ∧ p1)) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618125044481088294075909414550 : (((((p4 ∧ (p5 → (p2 ∨ p2))) ∧ (((True ∧ ((False → (True → p5)) → (p5 → ((False → p1) → (False ∧ p1))))) → False) ∨ p5)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_44499576739767396912654519222 : (((((p4 → p2) → (p3 ∨ ((p1 → (p5 → True)) ∧ True))) ∧ ((p4 ∨ p1) ∨ ((False ∧ (p4 ∧ p1)) → (p3 ∨ (p4 ∨ p2))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783272264914922992753574509794 : (((p3 ∨ ((p2 ∨ ((p2 ∨ p4) ∧ (False ∨ (p5 ∧ (True ∧ ((True ∨ (True → p5)) ∨ (p5 → p3))))))) ∧ ((False ∧ p3) ∧ (p4 ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641516745596413085646909133703 : (((((p1 ∧ p3) → (((((p3 → p1) → (True ∧ ((p1 → (p5 ∨ True)) ∨ p2))) ∨ (p3 ∨ True)) ∨ (p4 → p4)) ∧ (p5 ∨ p5))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245888123285090914119766732667 : ((p3 ∧ p5) ∨ (((((p3 ∧ (((True → p3) ∨ ((p4 ∧ False) ∧ (p3 ∨ (False ∧ True)))) ∨ (True ∨ p3))) ∧ (False ∧ p1)) ∨ True) ∨ p3) ∨ p5)) := by
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
theorem thm_5_vars_160530003907132706899839686235 : ((((p2 ∧ (True → (p3 → ((p4 ∧ p2) → True)))) ∨ (p1 → p4)) ∨ (p4 ∨ ((p5 ∧ p3) → p4))) → (p5 ∨ ((p1 ∨ p5) → (False ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115166303424691737058250317875 : ((((((True ∧ ((p3 → True) → p5)) ∨ True) ∧ p3) ∨ p5) ∧ (p1 → (p5 → (p3 ∧ (p1 ∨ (p5 → (p5 ∨ (p2 ∨ True)))))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45338106082295141231230984142 : (((p3 ∧ (p2 ∨ (False → ((p3 → ((((((True ∧ (p2 → p1)) ∧ p5) → (p2 → p2)) → (True ∧ p1)) → p5) ∨ p1)) ∧ True)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166031634484136647595084044711 : (((p1 → False) ∨ (((p5 ∧ True) ∨ p2) ∨ ((p3 → (p4 ∨ ((p2 → p5) ∨ p3))) → p1))) ∨ (p5 ∨ ((((p2 ∨ False) ∨ p1) ∧ False) → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340710501799224005346144915979 : (p2 → (((((False → (p3 → p3)) ∨ (False → False)) → (p4 → ((False → p5) ∧ (((p1 ∧ p1) ∨ (p3 ∨ p1)) ∧ (p4 → p5))))) ∧ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622655154471823495489977081299 : ((((p4 ∧ (((((True ∧ p3) → p4) ∨ ((False ∨ p3) ∧ (p1 ∨ ((False → p4) → p3)))) → p5) → (((p3 ∨ p1) ∨ p3) → p1))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219836594290970524471596809812 : ((p3 → ((p2 ∧ p2) → p5)) → (((p1 → p2) ∨ p2) ∨ (False → (p4 ∧ (True → (((True ∧ p5) ∨ ((p2 ∧ p2) ∨ True)) → (False ∧ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h2
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- False on the left can always be used.
    apply False.elim h2
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h2
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694858628556193213070315215600 : ((((p2 → ((p5 ∧ p1) ∨ (p5 → (((p3 ∧ p2) ∧ p5) ∨ (p2 ∧ p3))))) ∨ (p1 → ((False ∧ True) ∧ (((False ∧ p1) ∧ True) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649034830865613230747786563528 : ((((((True ∨ (((p3 ∨ False) ∨ (False ∨ ((False ∨ (p5 → p1)) ∧ (p2 → p4)))) → (True ∨ p1))) ∨ (True ∨ p5)) → p1) ∧ (p2 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112012487390770222541086790774 : ((((True ∨ ((p2 → p3) → p4)) → (p2 ∧ (p4 ∧ (((((p4 ∧ p3) → p5) → p1) ∨ p1) ∧ (p5 → (p1 ∧ False)))))) ∨ True) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50453069377259690236799623940 : (((p3 ∨ ((p3 ∨ (False ∧ (p5 → (p3 → ((p1 → False) ∨ (p2 ∨ p5)))))) ∨ ((p2 → p1) ∧ False))) ∨ (p5 ∨ (p1 → (p2 ∨ True)))) ∨ p5) := by
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
theorem thm_5_vars_53407605234193750474700138646 : ((((((p5 ∨ (p3 → p1)) ∧ p2) ∧ (p3 ∧ p2)) → (p4 ∧ True)) → (((False ∨ True) ∧ (((False → (p3 → False)) ∨ p3) ∨ p4)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184878499600134607227009319508 : (((p3 ∧ (p3 ∨ p1)) ∧ (((p5 ∨ (True ∧ p2)) ∧ p1) ∧ p2)) ∨ (p5 → ((p5 ∧ (False ∨ p5)) ∧ (p1 ∨ ((p1 ∧ (True ∧ False)) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119121186242187230507664713780 : ((p1 → (p1 ∧ (((((p5 ∧ (p5 ∧ p2)) → False) → (((p4 ∨ (p1 → (False ∨ p4))) → True) → (p4 ∧ p1))) → False) → p2))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116838389905981010289844481950 : (((True → p1) ∨ ((p1 ∨ (((((((p1 ∨ p3) → p4) → (True ∧ p2)) ∨ False) → p5) ∨ (p5 ∨ False)) → False)) ∨ (p3 → p3))) ∨ (p3 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77985605397427596351323314380 : (((p4 ∨ ((((((p3 ∧ (p2 ∧ p5)) ∨ (p5 ∨ (p4 ∧ p4))) ∧ False) ∨ True) ∨ (p4 ∧ (False ∧ (p3 ∧ (p3 ∨ p5))))) ∨ p3)) → p3) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ ((((((p3 ∧ (p2 ∧ p5)) ∨ (p5 ∨ (p4 ∧ p4))) ∧ False) ∨ True) ∨ (p4 ∧ (False ∧ (p3 ∧ (p3 ∨ p5))))) ∨ p3)) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601950908598642461822387851966 : ((((p4 ∧ (p4 ∨ ((((p1 → (p4 → p1)) → ((p3 ∨ p4) ∧ p5)) → p4) ∧ (False ∧ (p3 ∧ (p1 ∨ ((True ∧ p1) ∧ p2))))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117035734038618379804810479025 : (((p3 ∨ False) → ((p5 ∧ p2) ∨ ((p1 ∧ ((((False ∨ ((p3 ∧ p2) ∧ (p3 ∨ (True ∧ p3)))) ∧ p4) ∧ p5) → p5)) → False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655679697728946475800090789256 : ((((((((False ∨ p3) → ((p3 → (p2 ∧ p4)) → p5)) → True) → ((p4 ∨ (p3 ∧ p3)) ∧ p4)) ∧ (False ∨ (p5 ∧ False))) ∨ (p4 → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190917253392880586082300601224 : (((((p5 ∧ False) → False) ∧ p1) ∧ ((p5 → p5) → p1)) ∨ ((((((p5 ∧ p5) → (p4 ∧ (p4 ∧ p1))) ∧ p4) → (p4 → p5)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134861931417204740433498678450 : (((False → (((((True ∨ (((p1 → False) ∧ ((False ∨ True) ∨ p1)) ∨ (p1 ∨ p1))) → False) ∨ p3) ∨ p2) ∨ False)) → p2) ∨ (p4 → (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148844018881660994528293647151 : ((((p2 ∨ (False ∧ p4)) → p1) ∧ ((((p4 → (True ∨ p4)) → (p4 ∨ ((p5 ∨ p2) ∧ False))) ∧ p1) ∨ p2)) ∨ ((True → (p1 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9320864406340243576380079281 : ((((p2 ∧ ((p3 ∨ (p3 ∧ p4)) ∧ p1)) ∨ ((p3 ∧ False) → ((((p5 → (False → False)) ∨ True) ∨ True) ∨ (p4 → (True ∧ p5))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115235046905020053596450125921 : ((((p5 ∨ (((p3 → p2) ∧ p3) ∨ (True → p3))) ∨ p3) ∨ (p4 ∨ ((p3 → ((True → (p5 → p5)) ∨ (p5 → p2))) ∨ p5))) ∨ (p3 → p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195342973977614729826781310270 : (((True → ((True ∧ False) ∧ p4)) → (p1 ∨ False)) ∧ (p2 → (((p5 ∨ p4) ∨ (p3 → p2)) ∧ (p2 → (((p3 ∨ False) ∨ True) ∨ (False ∧ p5)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138033041702867277050567491311 : ((True → (((p5 ∨ ((p3 ∧ (False → p1)) → (p2 → (p2 → ((p4 → True) ∧ False))))) → p4) → (False ∨ (p1 ∨ True)))) ∨ (p5 → (p4 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_147943882502487983581996256655 : ((((p5 ∧ p1) ∨ (((p4 ∨ False) ∨ (((p4 ∧ (p1 ∧ True)) → (p1 ∨ False)) → p3)) ∨ p4)) ∧ (p3 ∨ True)) ∨ ((True ∧ (p3 ∧ p2)) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157144743803999704980757797955 : (((((False → (((p4 → p1) → (False ∨ p3)) ∨ (((False ∨ True) → p4) ∧ p3))) ∨ p4) ∨ p5) → p4) ∨ (((p4 → True) → True) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



