variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_822697997632101637667449073 : ((p4 ∧ ((False ∧ (((((((p4 ∧ p3) → False) ∨ True) ∧ ((True ∧ (p1 ∨ (p1 ∧ p3))) ∧ p2)) → False) ∨ p2) ∧ False)) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113127732662968951069254354928 : (((p1 → ((p4 ∨ p4) ∧ ((((False ∨ False) ∧ (((True ∧ (True → True)) ∨ True) ∧ p1)) ∧ p2) ∨ (False → (p4 ∧ p3))))) → p4) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139246281877636724437695199363 : ((((p3 ∨ False) ∨ (True ∧ (((p3 → True) ∧ p5) ∨ ((True ∨ ((p4 → (p3 → p2)) ∧ p1)) ∧ (True → p3))))) ∨ p5) → (p4 ∨ (p1 → p1))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h6 =>
        -- False on the left can always be used.
        apply False.elim h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671579082166439651011332865795 : ((((p5 → ((p4 ∨ ((p1 → ((False → (p3 ∨ ((((p5 → p2) ∨ True) ∧ p4) → p2))) ∧ p1)) → False)) ∨ p5)) ∨ (p2 ∧ (False → p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_111913953805461027803395532116 : (((((p3 ∨ (((True → (p4 ∧ (p2 ∧ True))) ∧ False) ∨ p3)) ∨ p4) ∨ ((p5 ∨ p4) ∨ ((p1 ∧ p4) ∧ (p1 → p2)))) ∨ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185837793664927326550055531888 : ((((p5 → (p2 ∧ ((p1 ∨ False) ∧ (p3 ∧ p3)))) ∧ p2) ∧ p5) → (p3 ∧ (((p2 → p4) ∨ p3) ∨ ((p5 ∧ p2) → (p4 → (True ∧ False)))))) := by
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
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h12
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- We need to get the left conjuct of h18 based on <expert-advice>.
  let h19 := h18.left
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114192863628318601643370452464 : ((((((p1 ∨ (True ∧ (p5 ∧ p1))) ∧ p5) → (p3 → p2)) ∨ (((False → p1) ∧ p2) → (p1 ∧ p3))) → (False ∧ (True → p3))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165664907447916219770178776060 : (((p2 ∧ (p2 → (p4 ∧ (p1 ∨ p5)))) ∨ ((p5 ∨ (True → (p4 ∨ p3))) ∨ (p1 ∨ True))) ∨ ((True ∧ p2) → ((True → (p1 ∧ p3)) ∧ False))) := by
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
theorem thm_5_vars_300100898076494103488424798535 : (False ∨ (((p5 ∨ (p1 ∨ (False ∨ (False → (True ∨ ((((p2 → p2) ∧ p5) ∧ p1) ∨ True)))))) → (p5 ∨ (p4 → (p5 ∧ p3)))) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185025077250484455361539166368 : (((p4 ∨ p3) ∧ (((((False → p2) → p2) → p5) ∨ p5) ∧ p1)) ∨ ((False ∧ (False ∨ (p4 ∨ (p3 ∧ (True → ((True ∨ p4) ∨ p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451460071570964921977316076454 : (((((((p3 ∨ ((False ∨ p1) ∧ ((True ∨ p2) → p4))) → (True ∧ p2)) ∧ False) ∧ (p3 ∨ (p1 ∧ p3))) ∨ (True ∨ ((p3 ∧ p3) ∧ p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_738016046999875597074081778384 : ((((True ∧ p5) ∨ (True ∧ (p3 → (p2 ∨ ((False ∨ ((((((p1 → (p5 → p4)) ∨ (p2 ∧ p2)) → p2) ∨ p4) ∧ p1) ∧ p5)) ∨ p3))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150294000670511808775534562547 : ((p4 → (((p1 ∨ ((p3 ∨ (p3 ∧ (((True ∨ p5) ∧ p2) → (p1 → p2)))) → p2)) ∨ p4) ∨ (p1 → p5))) ∨ (((p1 ∧ p4) ∧ p2) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230149084929147225017377730106 : (((p4 ∧ p2) ∧ p5) → (((True → True) → (((p1 ∨ True) → p5) → (((False → (p3 ∨ p1)) → p3) → p3))) ∨ (p4 ∧ (p4 ∨ (p5 ∨ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773581287436271321337989498364 : (((False ∨ (((p3 → (p5 ∧ p1)) → (((True → (p4 ∨ (p4 ∨ (False ∨ ((False ∨ (p4 → p2)) ∧ p1))))) ∨ (p3 ∧ p4)) ∨ p4)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_148837937054648900932717623472 : ((((p2 ∧ (p4 → p1)) ∨ p2) ∧ ((True → ((False → (p1 ∨ p3)) → (p3 ∧ p4))) ∨ ((p5 → p5) ∧ p5))) ∨ (((False ∧ p2) ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205450144934369164633093279264 : (((p4 ∨ (p5 → p1)) → (p2 → p1)) ∨ (p4 ∨ ((p2 ∨ p3) ∨ (((p3 ∨ (((p1 → (p3 ∨ p4)) → p2) ∨ True)) → (False ∧ p5)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (((p1 → (p3 ∨ p4)) → p2) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321045960770310321590669974783 : (p4 ∨ (p1 ∨ ((((p2 → p2) → False) ∨ ((p3 ∧ (p3 ∨ (p3 → (p5 → p1)))) → ((False ∨ (p2 ∧ ((True → True) ∧ p4))) → p4))) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65228826722689698703237998341 : ((p3 ∨ ((p1 ∨ ((p3 ∨ ((p3 → False) → ((p3 ∨ ((p1 ∨ (p3 ∧ p5)) → False)) ∧ False))) ∨ (((p3 → p1) ∨ True) ∧ p5))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147006113795287944044190086671 : ((((((p3 ∧ (True ∧ p3)) ∧ ((((p3 → False) → p1) ∧ p5) ∧ p2)) ∧ (p2 ∨ p2)) ∨ (p1 ∧ False)) ∧ p5) ∨ ((True → (False ∧ p3)) → p3)) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613925071423696103436982238321 : (((((((p3 ∧ ((True → (p1 ∧ (False → ((True ∨ p5) → p1)))) → False)) ∧ (p2 → True)) ∨ (p1 → p1)) ∨ ((p2 → False) ∨ p1)) ∨ False) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_148080649294342009397504968736 : (((((((((False ∨ p2) ∨ p1) ∨ (True ∧ p5)) → p5) → (p2 ∨ p1)) ∧ (True → p1)) ∨ False) → (False ∨ p3)) ∨ ((p5 ∨ False) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115964925459347978107014680718 : (((((p3 → p3) ∧ p5) ∧ p2) → (((True ∧ (p5 ∨ (p4 ∧ True))) ∨ (p3 ∧ p2)) ∧ (p3 ∨ (((p4 ∧ p5) ∨ p5) ∧ False)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165107675381551800243133456371 : (((p1 → (((p3 → (((True ∨ p4) → p4) ∧ True)) → p5) → (p4 ∧ (p5 → p5)))) → p4) ∨ (p3 → ((p1 ∧ False) → ((True ∧ p4) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253768315120680510599198849531 : ((p1 ∧ p1) → (p2 ∨ (((((p3 → p1) ∨ ((p4 ∧ True) ∧ True)) → True) → (p2 ∧ p5)) ∨ ((False ∧ False) → (((p2 ∨ False) ∨ p2) ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115784803025242623751744193495 : ((((False ∨ (True ∧ p2)) ∧ p4) ∧ ((p2 → ((p4 ∧ (False ∧ (p5 → (False → True)))) ∧ ((True ∨ True) → p1))) ∨ (False ∧ True))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260224823300626753358012425139 : ((p2 → p3) → ((p5 ∨ (p5 ∧ (True ∧ (p2 ∨ (((p5 ∨ False) ∧ ((p3 → False) ∧ ((p2 ∨ False) ∨ (p2 → p3)))) → (p3 ∨ p1)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174011612942257307105074368262 : (((p2 ∧ (((p5 ∧ p2) ∨ (p5 ∨ ((True ∧ True) → p1))) ∧ (p4 ∧ p4))) → True) → (p1 → (((p1 ∨ p3) ∨ (p3 ∨ p1)) ∨ (p1 ∨ p2)))) := by
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
theorem thm_5_vars_243435931240381216902617806124 : ((p5 → True) ∧ (True ∧ (((((p3 ∧ ((((p3 ∨ p4) → (p2 ∨ p4)) → (p5 ∧ p1)) ∧ p2)) ∧ (p3 ∨ p2)) ∨ (True → p5)) ∧ p4) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40382929505532050615668359729 : ((((((p4 ∨ ((False ∨ ((p2 → p1) ∧ p3)) ∧ ((False ∧ p4) ∧ ((True ∧ (True ∧ True)) ∧ p3)))) ∨ p1) ∨ (False → p1)) ∨ p1) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264295806402785477562818732569 : (True ∧ ((((True ∨ p2) ∨ (p4 → p5)) ∨ p4) → ((((True → (p2 → (p5 ∨ False))) ∨ (p1 → p2)) ∨ (False → (p2 ∨ p2))) ∧ (p3 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207851203263446995797307076404 : ((((p5 → p2) ∧ p4) ∧ (False ∨ p5)) → (((((p1 ∨ p5) ∧ p4) ∧ p2) ∧ ((False ∧ p1) ∧ (p3 ∨ p1))) ∨ (((p3 → p4) ∨ p3) → p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342529395865308387623301491304 : (p2 → ((p2 → ((False ∨ (((p5 ∧ (p5 ∧ p2)) → p2) ∧ (p5 ∨ p5))) ∧ p1)) → (p1 ∧ ((True ∧ p1) ∧ (((p2 → p1) → p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166965430355460855996273920174 : (((p2 ∧ (((False ∧ p5) → ((p5 ∨ p4) ∧ ((p3 ∨ p2) ∨ (True ∨ p3)))) ∧ p5)) ∧ p5) → ((((p1 → p4) ∨ (p4 ∨ p3)) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54687244501625828184257904137 : ((((p4 ∧ (((p2 ∧ False) ∨ p4) → p3)) → p4) → ((p2 ∨ (((((p1 ∨ ((p1 → p5) ∨ p4)) ∧ False) ∨ False) ∨ True) ∨ False)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64557685804162101566805746705 : ((p1 ∨ (((False ∧ (p2 ∧ p3)) ∨ True) → ((p5 ∧ ((p4 → (p5 ∧ ((p4 ∧ p4) ∧ (p4 ∧ (p3 ∧ p3))))) → p3)) ∨ (False ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245593869532186843941973306252 : ((p3 ∧ False) ∨ ((p3 ∧ ((p2 ∧ ((((p2 ∧ (False ∧ (p2 → True))) ∨ True) → p1) ∧ (((p3 → p1) ∨ False) → (p4 → p3)))) ∨ p1)) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : ((p2 ∧ (False ∧ (p2 → True))) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250086273237674323620573245348 : ((True → p4) ∨ (((((True ∨ p2) → False) ∧ ((p5 ∧ (True → p2)) ∨ True)) ∧ (p2 → ((False → True) ∨ ((False ∧ (p4 → p1)) → p1)))) → p1)) := by
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
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48183487207957318274706898809 : ((((p4 ∧ p1) ∨ (((((p4 → p3) → p5) → (p5 ∨ p5)) ∨ p1) ∧ (p3 ∧ ((p2 → p5) ∧ ((False → p1) ∨ p3))))) → (p4 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675548831881653972218468459947 : ((((((p5 ∧ p5) ∧ (((False ∨ (True → (p1 ∨ p2))) ∧ False) ∨ (True ∧ (p1 → p4)))) ∧ (p4 ∨ False)) ∧ (((True ∧ False) → p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215398079063206180727052543584 : ((p2 ∧ (p2 ∨ (p1 ∧ p5))) ∨ (((p1 ∨ True) ∨ p4) ∨ (p3 → ((p5 ∨ p1) ∨ (p2 ∧ (((p2 → p4) ∨ True) → ((p5 → False) ∨ p3))))))) := by
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
theorem thm_5_vars_247605121384230205086177120876 : ((False ∨ p5) ∨ (((False ∧ (p3 → ((p1 ∧ (False ∧ (False → ((p4 → False) → (p5 ∨ True))))) → True))) ∨ (p3 → False)) ∨ (p5 ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_133794230085808568697863053262 : ((((p1 ∧ (p4 ∧ True)) ∨ ((((True ∨ p2) ∨ (p2 → True)) ∧ (p3 ∧ (((True → True) → True) → p4))) ∧ p2)) ∧ p4) ∨ ((p3 → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701944748642392698196443520866 : ((((p2 ∨ (True → ((((True ∨ p1) ∧ p5) → False) ∨ False))) ∧ ((((p1 ∨ False) → ((((p2 ∧ p5) → p1) ∧ p1) ∧ p5)) ∧ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87232150322730955895742570273 : ((((p3 ∨ ((p1 ∨ p1) ∨ p3)) ∧ p1) ∧ ((p1 ∧ p1) → ((p2 → (((False → p1) ∨ p4) → ((p5 → p2) → p3))) ∧ (False ∧ True)))) → False) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h14 : (p1 ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h14
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : (p1 ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- We need to get the right conjuct of h20 based on <expert-advice>.
        let h21 := h20.right
        -- We need to get the left conjuct of h21 based on <expert-advice>.
        let h22 := h21.left
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h24 : (p1 ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h25 := h3 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147653304847444060670243698163 : (((((p4 ∧ (p5 ∨ (p4 ∨ True))) ∨ (p1 ∧ (p5 ∧ (((p1 ∨ p1) ∨ p1) ∨ p3)))) ∧ (p2 ∧ p1)) → False) ∨ ((False ∨ False) → (p4 ∨ p3))) := by
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
theorem thm_5_vars_111058674517815237522319993119 : ((((((True ∨ ((p5 → (p3 ∨ p2)) ∨ (p4 ∧ (p3 ∨ True)))) ∧ p1) → p2) ∧ (False → (((p2 ∧ p2) → p4) ∨ p2))) ∧ p3) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602030887984640416836292335395 : ((((p5 ∧ ((p4 ∨ (p5 → (p5 ∧ ((True ∧ True) → (p1 ∨ (((p3 → p5) ∨ (((True ∧ p1) ∧ p3) ∨ p2)) ∧ p1)))))) ∨ True)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59363216246712679807102206435 : (((p5 ∨ p3) ∨ (((False ∨ (((p1 → (p3 → (p3 ∧ p5))) ∧ p3) ∨ p3)) → (False ∧ ((p3 ∨ p1) → p2))) → ((p3 ∧ p3) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116583697450624049121536139320 : (((p4 ∨ False) ∧ (((p5 → (p2 ∧ p3)) ∧ p2) ∨ (True ∧ (p3 ∧ ((False ∨ ((p1 ∧ (False → (True ∨ p1))) ∧ True)) ∨ p5))))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55283491607169905553033468996 : (((False ∧ (p4 ∨ (p1 ∨ (p4 ∨ p2)))) ∨ (True ∨ (False ∧ ((p2 ∨ p5) ∨ ((False ∧ ((p5 ∧ ((p4 ∨ p4) ∧ p2)) → p5)) ∧ True))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172308137370461100953880033042 : ((((p2 ∨ p3) ∨ (p1 → (True → (p4 → p1)))) → ((p3 ∨ p4) ∨ (True ∧ p1))) ∨ (p4 ∨ ((p2 ∧ p4) → (((p4 ∧ p3) ∧ p1) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319367612194330081388079808079 : (p4 ∨ ((((((p1 ∧ (p5 ∧ p5)) → p1) ∨ False) ∧ True) ∧ ((p1 ∨ p5) ∨ p2)) ∨ (((p1 → ((p5 ∨ p4) ∨ (False → p1))) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_54936280708569218642689049205 : ((((p1 → (p2 ∧ (p5 ∧ p1))) → p2) ∧ (p5 ∧ (True → (((False ∧ p1) ∨ False) ∧ ((p3 ∨ p4) → (p5 ∨ ((p5 ∨ p5) ∧ p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211341417598534584449839424084 : (((p3 ∨ p1) ∨ (p5 ∨ True)) ∧ (((p4 → ((((True ∨ p4) ∧ (((p5 ∨ p2) ∨ p2) ∨ False)) ∨ (True → p3)) ∨ (p5 ∨ True))) → False) → p4)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((((True ∨ p4) ∧ (((p5 ∨ p2) ∨ p2) ∨ False)) ∨ (True → p3)) ∨ (p5 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262367494968518704992841507056 : (True ∧ ((((p4 → False) → p5) → ((p5 ∧ ((False ∨ p3) ∨ True)) → (p5 → (((p4 ∧ (p5 → p2)) ∧ p2) ∨ ((p4 → True) ∨ p1))))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750665300292854521297040199315 : (((True ∧ (((((p4 → ((p5 → p1) → False)) ∨ (True ∧ (p1 → p2))) → p5) → (False → p4)) → (p5 ∨ ((p1 ∧ (False ∨ p2)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352090316798679481968145616008 : (p4 → (((((p5 ∧ False) ∧ p1) ∨ p1) ∧ p3) ∨ ((False → p2) → (True ∨ ((False → (True ∧ ((False → ((p4 ∧ p5) → p4)) ∧ p5))) ∨ p4))))) := by
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
theorem thm_5_vars_251439152931223872845272044670 : ((p2 → p5) ∨ (((((p1 ∨ (False ∧ p4)) ∧ (p3 ∧ p2)) ∧ True) ∨ False) ∨ (True ∨ (p2 ∨ (p3 ∧ ((p1 ∨ False) ∧ ((p5 ∧ True) ∧ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52545631736112000643837640548 : (((((p4 → ((False → (p3 ∨ (p2 ∧ p4))) ∨ (p2 ∧ True))) ∨ p1) → p1) ∨ ((True ∨ (p5 ∧ p1)) → ((p4 ∨ p2) → (p2 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179180446998511969638297884109 : ((p3 ∧ ((False ∨ (((p4 ∨ p2) → (p5 → (True ∨ False))) ∧ p3)) ∨ p1)) ∨ ((p1 ∨ False) ∨ (p5 → (p3 ∨ (False → (p4 ∧ (False ∨ True))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346639324013840082641544147331 : (p3 → ((p2 ∨ (p5 ∨ ((p1 ∨ (p3 ∧ ((p4 → (p1 ∧ (p1 ∧ p4))) ∧ True))) ∨ (((p2 → p2) ∨ p2) ∨ p5)))) ∨ (True ∧ (p1 ∧ p3)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788497104459591180410630466929 : (((p5 ∨ ((p3 ∧ ((p5 ∧ (p5 ∧ ((p4 ∨ p4) → (p4 → ((False → ((p5 ∧ p2) → (p2 → (p4 ∧ p2)))) ∧ p3))))) ∧ p5)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_303930444912925161706145552642 : (p1 ∨ (((((p5 ∧ p4) ∧ False) ∨ ((p5 ∨ p5) → False)) ∨ (p1 ∨ (p1 → (p3 ∨ (((p4 ∧ False) ∨ (p3 ∧ False)) ∨ (True ∧ False)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264318459908866103698324699602 : (True ∧ ((False ∨ (((p4 ∧ p3) ∧ p5) → p4)) → (((False ∨ ((((False ∨ False) → True) ∧ (True ∧ p5)) → p3)) ∨ True) ∨ (True ∧ (p2 ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115809057412550147221808251803 : ((((p4 ∧ (p1 → p3)) → True) ∧ ((((p1 ∨ False) ∧ ((((False → False) → p5) ∨ True) → p1)) ∨ (p4 → (p5 → p5))) → p4)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156930621317120551539238556841 : ((((((True ∧ (p1 ∧ (p2 → ((p1 ∧ p2) → p1)))) → (p1 → p4)) → p1) ∧ (p5 ∨ True)) ∨ p5) ∨ ((p4 ∧ (p4 ∧ p2)) → (p4 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112012533330953060764529708427 : ((((True ∨ (p2 ∨ (p1 ∧ p4))) → (((p5 ∧ (p1 → (False ∧ (p2 → (p3 ∨ True))))) ∨ (True ∨ p3)) ∧ (p4 → True))) ∨ p3) ∨ (p4 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304039085557017866656054684825 : (p1 ∨ ((p3 ∧ (p3 → ((((p2 ∧ (False → True)) ∨ True) ∧ (((p2 ∧ p2) → (p2 → (((False → p5) ∨ p1) ∧ p3))) → False)) ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811739305773393779499862880491 : (((p5 → (p4 → ((((True ∧ (((p2 ∨ p3) ∧ (((p2 ∨ p4) → (p3 ∨ p1)) → (p4 ∨ p4))) ∨ False)) ∧ (p3 ∨ p2)) ∧ False) ∨ p4))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57873045991994287258496196770 : (((p1 ∨ (p1 ∨ p4)) → (((((((True → p4) ∨ True) ∨ (p1 ∨ p2)) → False) → (p1 → p2)) ∨ (True ∨ ((p2 ∧ p1) ∧ True))) ∨ p5)) ∨ p4) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340967622793082463125848333618 : (p2 → (((p1 ∨ p4) ∧ (((p1 → False) ∨ ((p5 → True) ∧ (p2 ∧ (p4 → (p4 ∨ ((p3 ∨ (True ∧ True)) ∨ p5)))))) → (p5 ∧ p5))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44094295435416047832066752528 : ((((p4 ∨ (False → (p2 → (((p1 ∧ p2) ∧ (p4 → p5)) → ((p4 ∨ (p2 → p1)) ∨ (p3 ∨ p3)))))) ∧ (p2 → (p5 ∨ p1))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115533411575713207392622384607 : (((p5 ∧ ((p4 ∧ ((True ∧ False) ∧ False)) → p1)) → (((p3 → (False → p1)) ∨ p3) → ((p3 → p1) ∨ ((True ∨ False) ∨ p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219002047920263903243051111911 : ((p4 ∧ (p2 ∨ (p1 ∧ p5))) → ((((p5 ∨ False) → p5) → True) ∧ ((p3 ∨ ((p2 ∨ ((p4 → p1) → True)) ∧ (p1 ∨ False))) ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399602717776389255094278265492 : ((((p3 → ((((False ∨ ((True → (p4 ∨ p1)) ∨ p1)) ∨ False) ∨ (((p1 ∧ (True → (p2 ∨ p1))) → p2) → (p5 ∧ p5))) ∧ p5)) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_115461795332605897282946498695 : (((False ∧ (p1 ∨ ((p1 ∨ p4) → (p2 ∨ True)))) ∨ (((p1 ∧ p5) → ((p5 → False) ∨ ((p4 ∨ True) ∧ p2))) ∧ (p5 ∨ p5))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355569117384402712012085626679 : (p5 → ((((p5 → ((((p1 ∨ (p2 → p3)) → False) ∧ (p2 ∧ p1)) ∧ False)) ∨ (p1 → (p5 → p2))) ∧ (False ∧ (p5 ∧ False))) ∨ (p1 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137376310866697619380110124845 : ((p3 ∧ (((((p3 ∧ True) → p3) ∨ (p4 → p3)) ∧ ((p1 → p3) ∨ p5)) → (((p5 ∧ p2) → False) ∨ (p3 ∧ p3)))) ∨ (p5 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160139590905394806621562054352 : ((((((p1 ∨ (p2 → p5)) → (p4 ∨ (p2 ∨ (p2 → (p4 ∨ p2))))) ∨ p5) → p2) ∧ (p3 → p1)) → (p4 ∨ (p2 ∧ ((p2 ∨ True) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 ∨ (p2 → p5)) → (p4 ∨ (p2 ∨ (p2 → (p4 ∨ p2))))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324266171155466496990528867542 : (p5 ∨ ((((p1 → p5) ∨ True) → ((p2 ∧ p4) ∧ False)) ∨ ((False → (p2 → p4)) ∨ (p4 ∨ ((p3 → (p5 ∨ True)) → (False ∧ (False ∨ p1))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116358655891144917530002822057 : ((((p3 → True) ∨ True) → (((((False ∨ p5) ∨ True) → p2) → (p4 → p1)) ∨ ((False ∨ (True ∧ ((p4 ∨ True) ∨ False))) ∨ False))) ∨ (p2 ∧ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594604873960432027012115698805 : (((((p2 → ((((p3 ∨ ((p4 → p3) ∧ False)) ∨ ((False ∧ True) ∨ False)) ∧ p3) ∨ p3)) ∨ ((p1 ∨ p4) → (p5 ∨ (p3 ∨ p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196940719169665457960345155220 : (((((p1 ∨ (p1 ∨ p4)) ∧ p4) ∨ p3) ∨ p5) ∨ (p4 ∨ ((True ∨ (((p1 ∨ p3) ∨ p5) → False)) ∨ (((False → p2) ∨ (p2 ∨ p2)) ∧ p2)))) := by
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
theorem thm_5_vars_258670642232537401493273827647 : ((p5 ∨ p5) → (((p1 ∧ p3) ∨ (p4 ∧ p3)) ∨ (True ∨ (((p1 ∨ ((p4 → ((p4 ∨ p1) → p4)) ∨ False)) → (p1 → p1)) → (p5 ∧ p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192969490053827047973293365860 : (((p4 ∨ (((p2 → p3) ∨ True) ∧ False)) ∨ (True → p4)) → ((p3 ∧ ((p5 ∧ p5) ∧ (True ∧ (False ∨ (p4 ∨ (p2 ∧ (p3 ∨ p5))))))) ∨ p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h6
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266164634095492848949469037882 : (True ∧ (p3 → (p2 ∨ (((p2 ∨ (p1 → (True → (p5 → ((p4 ∧ p2) ∧ ((p3 ∧ (p1 ∧ p1)) ∨ True)))))) → (True → p2)) ∨ (p2 → p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149713171516168913611703838810 : ((p5 ∧ (p4 ∨ ((p5 ∨ p5) ∧ ((((((p5 ∧ p4) ∨ p4) ∧ p2) ∨ p2) ∧ (False ∧ (False ∧ p3))) ∧ p4)))) ∨ ((False ∨ (False ∧ False)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769063290971002016620650602044 : (((p5 ∧ (((p3 ∨ p2) ∨ p3) → (p4 ∧ ((p1 → (((True → (True ∧ (p3 ∧ (((p5 ∧ p1) ∧ False) → p1)))) ∧ p3) → False)) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136853862469931819839792196927 : (((p4 ∧ p2) ∨ (True → (((p3 → True) ∧ (p4 ∨ (p1 ∨ True))) → (((p2 ∧ p5) → (p4 → (False → p1))) ∧ p4)))) ∨ ((True ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41065493024732636546069425925 : ((((True ∨ (((((((p2 ∨ p4) ∧ False) → p3) → (False ∨ (p5 ∧ p5))) ∨ True) ∨ (p3 ∨ True)) ∧ (p3 → p4))) → (p4 ∨ p5)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201964199709379775077236448143 : (((p5 ∨ (p1 → (p3 ∨ True))) ∨ p4) ∧ ((((p3 ∨ False) ∨ p4) ∨ (False → (p4 ∨ (True ∨ p1)))) ∨ ((p4 ∧ ((p4 ∧ False) → False)) → p3))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342780885480485922981527614159 : (p2 → (((p4 → ((p1 ∨ p3) ∨ (p5 ∨ p2))) ∨ False) → (p5 → ((((p1 ∧ ((p2 ∨ p5) → p1)) ∧ p4) ∧ (False ∨ p2)) ∨ (p5 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341674974615926105425863065775 : (p2 → ((((p5 ∧ p4) ∧ (((p1 ∧ False) → (p4 → p4)) → (((p4 ∨ (p5 ∧ False)) ∨ (p5 ∨ p4)) ∨ (p2 → p5)))) ∨ True) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809124447443387391683451952994 : (((p5 → (((((p3 ∧ p1) → (((p5 → (p4 → False)) ∨ False) ∨ (p1 ∨ ((p5 ∨ False) ∧ p1)))) → (True → (p3 ∧ p1))) ∧ p4) ∨ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_164996981149557922018599510981 : ((((p3 ∨ (False ∧ (p1 ∧ ((False → p4) ∧ p1)))) ∧ ((p1 ∨ p1) → (p4 ∧ p1))) → p1) ∨ (((True → p1) → p1) ∨ (p1 ∨ (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_740502987381941105597388085896 : ((((p1 ∨ p5) ∨ (True → (((p5 ∨ p2) → (True → p1)) → ((((p1 ∧ (((p5 ∧ p2) → p1) ∧ p1)) ∧ p1) ∨ p2) ∨ (p3 → p3))))) ∨ False) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219320437920870422572704442466 : ((p2 ∨ (p1 ∧ (True ∨ p2))) → (p5 ∨ (((p5 ∨ p4) ∨ (p3 ∨ p4)) → (p3 ∨ (p4 → (p5 ∨ (True → (False ∨ (p2 → (p5 → p4)))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h28
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h30
          -- Implications on the right can always be decomposed.
          intro h31
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h36
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h37
          -- Implications on the right can always be decomposed.
          intro h38
          -- One of the premise coincides with the conclusion.
          exact h35
    case inr h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h40
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h42 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h43
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h42
        case inr h44 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h45
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h46
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- One of the premise coincides with the conclusion.
          exact h45
      case inr h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h50
        case inr h51 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h52
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h53
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h54
          -- Implications on the right can always be decomposed.
          intro h55
          -- One of the premise coincides with the conclusion.
          exact h52



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246156425568399332731177532671 : ((p4 ∧ p2) ∨ ((p4 ∨ ((False ∧ False) ∨ ((p4 ∨ p4) ∨ (p2 → p2)))) → (p1 → ((p2 ∨ p3) ∨ (True ∧ ((False → p3) ∨ (p2 ∨ p4))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
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
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
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
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670265434388052021170549030301 : ((((((True → True) ∧ (p5 → False)) → (p2 → ((((False → p1) ∧ ((p1 ∨ p1) → p5)) ∧ False) ∧ (p1 → False)))) ∨ ((p5 → p4) → True)) ∨ p3) ∧ True) := by
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



