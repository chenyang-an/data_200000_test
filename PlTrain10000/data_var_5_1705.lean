variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98997725033511788086841720324 : ((True → (((p2 → (False ∧ ((False ∨ p4) ∨ False))) ∨ ((False ∨ p4) ∨ p4)) ∧ ((p2 ∧ p3) ∧ ((p3 ∨ (p2 ∧ p2)) ∧ (True → p1))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199941364049562160130049000933 : (((p3 ∧ ((p4 ∨ p3) ∧ p2)) ∨ (p3 ∨ p2)) → ((p3 ∧ ((((p4 ∨ p1) ∨ p5) → (False ∧ p1)) → p4)) → ((p4 ∨ False) ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319178803441763987382022051450 : (p4 ∨ (((p5 ∨ False) ∨ (False ∨ ((p5 ∨ (p1 ∨ ((p5 ∧ False) ∧ p4))) ∨ (True ∨ (p5 ∨ p5))))) ∨ ((False ∨ (p1 ∨ (p1 ∨ False))) ∧ p4))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44893028095873608833201936343 : (((((p5 → True) → p4) → ((p2 ∨ (p4 → (((p1 → (True → False)) → ((p3 ∨ p1) ∧ (p1 → p3))) ∨ True))) → (p4 → p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241820845704828623829898763363 : ((p1 → p1) ∧ (((((((p4 ∨ (True ∧ (p2 ∧ p4))) → True) → p4) ∧ (p3 ∧ ((p2 → p4) ∨ p4))) ∨ p2) → (p4 → (True ∧ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206111475297740779352630159082 : ((p4 ∧ ((p5 ∧ (p3 ∧ p2)) ∨ p1)) ∨ ((p2 ∨ (p5 ∨ p2)) → ((p3 → (True ∨ (p5 → p3))) ∨ (p2 ∧ (((True ∧ True) ∧ p2) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66271128859196402655752925313 : ((p5 ∨ ((True ∧ (p2 → p3)) ∨ (((True → (((False → (p2 ∨ True)) → p5) ∧ True)) ∧ p3) → (((p3 ∨ True) ∧ p5) ∨ (p4 ∧ True))))) ∨ p3) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (False → (p2 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641464519418392173511174921943 : (((((True ∧ p3) → ((p5 ∧ ((False ∧ (((p4 → True) → ((p2 ∧ False) ∨ (p3 → p2))) → p2)) ∧ (p1 → (p2 → p4)))) ∧ p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165521275747522519695677083564 : ((((p1 ∧ (p1 ∧ True)) ∨ ((p3 → p3) → (p3 ∧ True))) → ((p2 ∨ p4) ∧ (p1 ∨ p5))) ∨ (p1 ∨ (p5 → ((p5 ∧ True) → (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749148392344392021902188480086 : ((((p5 → p1) → ((p4 → (False ∨ (False ∧ (True → p2)))) ∨ ((((p5 ∨ True) ∧ (p2 ∧ (True ∧ p1))) ∧ (True ∨ (p3 ∧ p4))) → p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h6.left
    let h18 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346423591655710414863627924495 : (p3 → ((((((p4 ∨ p1) ∧ (p1 → p5)) ∨ ((p3 → ((p5 → True) → (p1 → False))) ∧ (p4 ∧ p3))) ∨ (p4 ∧ p4)) → p3) → (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299144955646989791645516364003 : (False ∨ ((((p2 ∨ (p2 ∧ p1)) ∨ (((p4 ∧ (p2 ∧ p3)) → p1) ∧ ((p5 ∨ p1) ∧ ((p4 → (p5 → (True ∧ p1))) ∨ p2)))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69140442699477028621558295003 : ((p5 → (((((p1 ∨ (p1 ∧ p3)) ∧ p2) ∨ ((((True → p5) ∨ p2) ∨ (p1 ∧ (p1 ∧ p4))) ∧ p2)) ∨ False) ∨ ((p2 ∨ p1) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304015297023463021470481498540 : (p1 ∨ ((True ∧ (True ∧ (p2 ∨ ((((True → p4) ∨ True) → True) ∧ ((False ∧ True) ∧ ((((p1 ∨ p5) ∨ True) → (True ∧ p5)) ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53371351217310890380699910639 : (((((((p4 → (p5 ∨ p2)) → (True → True)) ∨ p5) ∧ True) → p3) → (p2 ∧ (((((p3 ∧ True) ∨ p4) ∨ p2) ∨ (p1 ∨ p3)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25252014689351664135409396461 : ((((p5 → p3) ∧ p5) → (((p1 → p2) → (False ∨ (((p5 ∧ (p3 → (p4 → (p5 → p2)))) ∧ p2) ∨ (p1 → p3)))) ∧ (p5 → p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244312767258880955758855320876 : ((False ∧ False) ∨ ((p1 ∧ ((p1 → ((False ∨ ((False ∧ ((p1 ∧ True) → ((p3 → p5) → p2))) ∧ (p5 ∨ p3))) ∧ (p5 ∨ p5))) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67917712362769564091544798116 : ((p2 → (((p4 ∨ ((False ∨ (p2 ∧ p3)) ∧ p5)) ∨ ((p1 ∨ p2) → p5)) → ((((True ∧ (True → p3)) → p5) → (p3 ∧ p5)) ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302618596452251850639987202175 : (False ∨ (p2 ∨ ((((p5 → ((True ∧ p1) ∧ (p3 ∧ (p2 ∧ p5)))) ∨ ((p4 ∨ ((p3 → True) ∨ p1)) ∧ (p3 ∨ True))) → (p3 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311854247714001109037627207344 : (p2 ∨ (p1 ∨ (p2 → (((p2 ∨ p3) ∧ (p3 ∧ (((((p5 ∨ p5) → False) → (p4 ∨ p4)) ∨ p5) ∧ p5))) ∨ (False → (p3 ∨ (False ∨ p3))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243764867144590573189364033560 : ((p5 → p5) ∧ (((p5 ∨ (((p5 ∨ ((p5 → p5) → p3)) ∧ False) ∨ p4)) → ((p3 ∨ p3) ∨ ((((False → False) ∧ p4) ∧ p2) ∨ p2))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118799592858307401892958861636 : ((True → (((p3 → (((p5 ∨ p1) ∨ False) → (((False ∨ (True → (p5 ∨ ((p3 ∧ p5) ∧ p3)))) ∧ p4) ∧ p4))) → p5) ∧ p4)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_906758987763874645825339168793 : (((((((p5 → (p5 → (False → p3))) ∧ ((((p1 ∧ p2) ∧ p4) ∧ p2) ∨ True)) → p1) → (True → p1)) → ((False ∧ (p3 ∨ p3)) ∨ False)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p5 → (p5 → (False → p3))) ∧ ((((p1 ∧ p2) ∧ p4) ∧ p2) ∨ True)) → p1) → (True → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p5 → (p5 → (False → p3))) ∧ ((((p1 ∧ p2) ∧ p4) ∧ p2) ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343586699116649660864931311366 : (p2 → ((p1 → p3) → (((((p3 ∨ False) ∨ p4) ∧ p2) ∨ p2) → (p2 → (((((((p2 → p4) ∧ p2) → p2) ∨ True) ∧ p1) ∨ p3) ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173937782588296894608464841362 : (((((p2 ∧ (((False ∧ p5) ∨ p2) → p5)) ∨ p5) ∧ ((p4 ∧ False) → p5)) → p4) → (((p2 → p5) ∨ ((p5 ∨ (False ∧ False)) → p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p2 ∧ (((False ∧ p5) ∨ p2) → p5)) ∨ p5) ∧ ((p4 ∧ False) → p5)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h4
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111703321813797247934017808393 : (((((((False → ((p1 ∨ p1) → ((p3 ∨ (p1 ∧ False)) → True))) ∨ (p2 ∨ p5)) ∧ (p4 ∧ False)) → (p2 ∨ True)) → p3) ∨ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203630991567627143842980519407 : ((p2 ∨ (p2 → ((True ∨ False) ∨ p1))) ∧ (((((((p1 → ((p1 → False) ∧ p5)) ∨ p5) ∧ (True ∧ p2)) ∧ (p5 ∧ p2)) ∧ False) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47294652360640277211186494022 : (((((p3 ∧ p1) ∨ False) ∧ (((p2 → (True ∨ p3)) → (p3 ∧ p2)) ∨ (p2 ∧ (p2 → ((False ∨ True) → (p4 ∧ True)))))) ∨ (p4 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45822222217437068714588255223 : (((p2 → ((p2 ∧ (((p1 ∨ (p1 ∧ (p4 ∨ p2))) ∧ p5) → (((p2 → (((p4 → p3) ∧ p4) ∨ p1)) ∨ p1) ∧ p4))) ∨ p4)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678476156540147232961880893133 : (((((False → (True ∨ (p5 → True))) → (((p5 → (p5 ∨ True)) ∧ (((p5 ∧ False) → False) ∨ p1)) ∧ p1)) ∨ (p2 ∧ (True ∧ (p5 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247830952418655234395583975359 : ((p1 ∨ p2) ∨ (((((((p2 → (p5 ∨ p2)) ∨ ((p2 ∧ p5) ∨ (p5 ∨ (p2 → p4)))) → p3) ∨ (p3 → (p2 ∨ False))) ∨ True) ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314021366092791962843523261795 : (p3 ∨ ((p3 ∨ (((True → ((p3 → False) → p5)) ∧ ((p3 ∧ (p4 ∧ (p1 → (False ∧ (p2 → p4))))) ∧ p2)) ∧ (p5 ∨ p4))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115558117345877151979224613478 : ((((((p4 ∨ p2) ∧ True) ∧ p4) ∨ p1) ∧ ((p2 → (((p1 ∧ p4) ∧ (p4 ∧ p5)) ∧ (False ∧ (p5 ∧ (p4 ∧ p4))))) → p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230553042651377132116407889261 : (((False → p4) ∧ p4) → ((((p3 → (p2 → (p1 ∧ True))) → p1) ∨ ((True ∨ (p4 ∨ (p4 ∧ (p2 ∨ p3)))) ∧ (True ∨ p5))) ∧ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300656945249351818605095384824 : (False ∨ ((p4 ∨ (((False ∨ ((((p1 → p3) → p3) ∧ False) ∨ True)) → (p4 ∨ (p3 ∨ True))) ∨ True)) ∧ ((p5 ∧ p5) ∨ (p3 → (p3 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45679302423572186810191574922 : (((p5 ∨ ((p3 ∧ ((p2 ∧ ((True ∧ False) ∧ p1)) ∧ p3)) → (((((p3 → p4) ∨ ((False ∨ p1) ∨ p2)) ∨ False) ∧ p3) → p5))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161055133178249944950583640990 : (((p2 ∧ (p2 ∨ False)) → (((((p3 ∨ p3) ∧ ((True ∧ (p2 → p1)) ∧ True)) ∨ p1) ∧ p3) ∧ p5)) → (((True → p3) ∨ True) ∨ (p2 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190678816939279494635771636553 : (((p3 → (True ∧ ((True ∧ False) → (p4 ∨ False)))) → False) ∨ (((p4 → p4) ∧ (p4 ∧ ((False → p3) → (p5 → p5)))) → (False → (p3 ∧ p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759259798596671138703221873154 : (((p2 ∧ ((((True ∧ (((p4 ∨ (p1 ∨ p4)) ∨ (True ∨ (p1 ∨ p2))) → (p4 ∧ p4))) ∨ p5) ∧ (True ∧ (p4 → p3))) → (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325975036277494108147453027448 : (p5 ∨ (True → (((((p1 → (p4 → p4)) → ((p2 ∨ (True ∧ False)) ∨ ((p4 ∨ p4) ∧ p1))) → ((p1 ∧ p5) ∨ (p1 ∨ True))) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173196235225595986591978991809 : ((p5 ∨ (((True → (False ∧ p1)) ∨ (p5 ∨ (p1 → (p1 ∧ (p4 ∧ p3))))) ∧ p1)) ∨ (((False ∧ p2) ∨ (True ∧ p4)) ∨ ((p1 ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225735776172429993181090950235 : (((p4 → p2) ∧ True) ∨ ((((False ∨ False) ∧ (p4 → p3)) ∨ (False → (p4 ∧ (p3 ∧ p2)))) ∧ (((p5 ∨ (p2 ∧ (p2 ∨ True))) → p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158773127159553367983483375686 : ((p4 ∧ (p3 ∨ (((p1 ∧ (p5 ∧ p1)) ∨ p3) ∨ (((p5 ∨ False) ∧ p3) → (p4 → (False ∨ True)))))) ∨ (((False ∨ (p2 ∨ p5)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256043064664942121490893462683 : ((True ∨ p4) → ((((p2 ∧ p4) ∨ ((p5 ∨ p3) ∨ False)) ∨ (((False → ((p5 ∧ p5) ∨ p1)) ∨ ((p5 ∨ False) ∧ False)) ∨ p2)) ∨ (True → False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154640426533915487825138662267 : (((((False ∨ ((p2 ∧ p4) → p3)) ∧ ((p3 → (False ∨ False)) ∨ (p2 ∨ False))) ∨ True) ∧ (p2 → p2)) ∧ ((((p1 ∨ False) → p2) ∨ p1) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118131545406237640959818284505 : ((False ∨ (((p2 ∨ p2) ∧ (p4 ∧ ((p3 → (((p1 ∨ p5) → p4) ∨ (p5 ∧ p5))) ∨ (True ∧ p3)))) ∧ (p5 ∨ (p5 → False)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717446180849242566872418331105 : ((((False → (p4 → (p2 → p5))) ∧ (((((False ∧ False) ∧ (True → (p4 → p2))) ∨ p5) ∨ p5) → (p3 ∧ (False ∨ (p4 ∧ (p3 → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266253282538220075442354376387 : (True ∧ (p5 → (((p5 → ((False ∨ True) ∨ True)) ∧ (p3 ∧ ((p2 → (p4 ∨ (p4 ∨ False))) ∨ ((p3 → (p3 ∧ p1)) ∧ p4)))) ∨ (p1 ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118603466829153427966653518819 : ((p4 ∨ ((((p2 → p1) → (p3 → ((True ∨ (p2 ∧ False)) ∧ (False ∨ p2)))) ∨ ((p5 ∧ p2) ∨ p3)) ∧ ((True ∧ p3) ∨ p5))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205164198421750829035156894897 : (((p4 ∧ (p2 ∧ p2)) ∧ (p2 ∨ p3)) ∨ ((((p3 → ((p2 → p2) → True)) ∨ True) → (p4 ∧ (p2 ∧ p3))) ∨ ((p5 ∨ (p1 ∨ True)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619797548627783007478090963813 : (((((p2 ∨ True) ∧ ((True ∧ (((False ∧ (p3 ∨ p3)) ∧ p2) ∧ ((p4 → p5) → (p1 ∧ (False ∨ (p2 ∨ True)))))) ∨ (p2 ∧ p2))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137291560894167421021547586847 : ((p2 ∧ ((p4 → ((((False → (p3 → (p1 ∧ (p3 ∨ p1)))) → (((p2 → False) ∨ p2) ∧ p5)) ∨ p4) → p2)) ∨ p5)) ∨ (p1 → (p1 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48576015470464730684883542256 : ((((True ∨ (p4 ∨ ((((False ∨ (True ∨ (p3 ∨ True))) → (False ∨ (p4 ∧ p2))) ∨ p2) ∨ (p5 → p1)))) → p5) ∧ (p1 ∨ (False ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218411142074186772082471897416 : (((False ∧ p4) → (p2 → p2)) → (p5 ∨ (((p3 → (p2 ∧ p3)) ∨ ((False → (p4 ∨ p1)) → ((p3 ∧ False) ∧ p4))) ∨ ((p3 ∧ False) → p2)))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135523901522477685669530454168 : (((((False ∧ p1) ∧ (((p3 → ((p5 ∨ False) ∧ (p3 ∨ False))) ∧ p4) ∨ p1)) ∨ True) ∧ ((p2 ∧ (True ∧ p1)) ∨ p2)) ∨ (False ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774819310555333018346390692771 : (((False ∨ ((p4 ∨ (p2 ∧ ((p1 ∧ True) → True))) → (p2 ∧ (p4 ∧ (((True ∧ (((p2 ∨ p1) ∧ p3) → (p5 → False))) → p5) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669138653756226242641151528975 : ((((((False ∨ (p4 ∧ (p1 → (p3 ∧ (False ∧ p1))))) ∨ (p5 → ((((True ∧ False) ∧ p4) ∨ p2) → p5))) → p1) ∨ (p1 → (p1 ∧ True))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677009264110276757550166621065 : ((((p1 → ((p3 ∧ True) ∨ (((p4 → (p2 → p2)) ∨ p4) ∨ (p1 → (((p5 ∧ p2) ∧ False) → True))))) ∧ (((p1 ∨ p2) ∨ p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64270926125340389010036026413 : ((False ∨ (True → (p2 ∧ (False ∧ ((p5 ∨ p4) ∨ (((((p5 → (p5 ∧ (p5 → p4))) ∨ (p5 → p1)) → p5) ∨ (p5 ∧ p3)) ∨ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216363381987947198166109616612 : ((p3 → ((True ∧ p3) → p5)) ∨ ((p3 → p4) ∨ ((False ∨ ((((p3 ∨ p1) ∧ True) ∨ ((p5 ∧ False) ∨ p5)) → (p1 ∧ p4))) ∨ (True ∨ p5)))) := by
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
theorem thm_5_vars_127283291736532301555021648044 : ((p2 ∨ ((p4 ∨ (p3 ∨ (((p4 → (p5 → (p5 ∨ False))) ∨ p1) ∨ (((p2 → p4) ∧ p3) ∨ (p2 ∨ (p5 → p1)))))) → p1)) → (p2 ∨ p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p4 ∨ (p3 ∨ (((p4 → (p5 → (p5 ∨ False))) ∨ p1) ∨ (((p2 → p4) ∧ p3) ∨ (p2 ∨ (p5 → p1)))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173953281655877490581343042165 : ((((((p1 → (p4 ∨ p4)) ∨ p5) ∨ p5) ∨ (p3 ∨ ((p3 ∨ p5) ∧ True))) → p1) → ((True → p1) ∨ ((p1 ∨ p4) ∨ ((p1 → True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3465157586491324270056292062 : (True ∧ (True → (p4 → ((((p3 → (((((p3 → p1) ∨ p4) ∧ True) ∨ p1) ∧ p5)) → p5) ∧ (((p5 ∨ p3) → p2) ∨ True)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185293471208827691657028494879 : ((p2 ∧ ((p4 ∨ p3) ∧ (p1 ∨ ((True ∧ p1) → (p2 → p5))))) ∨ (p1 → ((((((p4 ∧ True) → (p3 → p2)) → False) → p4) ∨ True) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247484423919806434153492361781 : ((False ∨ p3) ∨ (((p5 → (((p4 → True) ∧ (((p5 ∨ (True ∧ p4)) ∨ True) → (p4 ∧ True))) → (True ∧ False))) ∨ p5) → ((p2 ∧ p4) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135873018870984416038386009330 : (((((False → True) → p4) ∧ ((True ∧ p4) ∨ (False → (p4 ∨ p5)))) ∨ ((((p2 ∧ p5) ∨ p3) ∧ (True ∧ p5)) ∨ p3)) ∨ (p3 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672779543906405035430768847962 : (((((p2 ∨ ((False → (((True ∧ (True ∧ (p4 → p2))) ∨ p2) ∧ p3)) → ((True ∨ p4) → p4))) → (p1 → p4)) → ((True → p5) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47071662306060382804277992066 : ((((p2 ∨ ((((((True ∧ (p3 ∧ (p1 ∨ False))) → p1) ∧ p5) ∨ (p5 ∨ True)) → False) ∧ (p5 ∨ p4))) ∨ (p4 → p2)) ∨ (p4 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190413335256183382780612475676 : (((False ∨ (((False ∧ (p4 ∨ True)) → p3) ∧ p2)) ∨ p3) ∨ (p2 → (True ∧ ((p3 → p3) → ((p3 ∨ (p3 → (False ∧ p3))) ∨ (False → p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350268888952270552033218079118 : (p4 → ((p3 ∧ (p1 ∨ ((((((p5 ∨ (p1 ∨ False)) → (p3 → (p1 ∨ (p4 → p3)))) → False) ∧ p1) ∧ (p3 → (False → p3))) → p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317918617035426108325143858660 : (p4 ∨ ((p5 ∧ (p5 ∧ (True ∧ (((((p3 ∧ True) → p3) ∧ p5) ∧ ((p1 ∨ True) ∧ ((p4 ∧ p1) → p5))) ∧ (False ∨ (p3 ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50285463385915393653911385022 : ((((((p4 ∧ p5) ∨ p5) ∨ ((False ∨ (p3 → p1)) ∧ (p4 → (False ∨ (True → p5))))) → (False ∧ p1)) ∨ (p2 → ((p5 → p2) ∨ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118811973056319389672372341976 : ((True → ((((p5 → ((p5 ∨ True) ∨ p1)) ∧ ((((p5 → p2) ∧ p3) → (p1 ∨ True)) ∧ p4)) → (False ∧ (p1 ∧ p3))) ∨ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612576930744445784464638354973 : (((((((p1 ∧ p5) ∨ (p2 ∨ (p5 → (p2 ∨ (((p4 ∧ ((p1 → p1) ∨ p1)) → p1) ∧ (p2 ∨ p1)))))) → False) ∨ (p2 ∨ p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264531021088446243063545644902 : (True ∧ ((p4 → (p2 → p4)) ∧ ((((p3 ∧ False) ∧ (p3 ∨ True)) ∨ (((p5 ∨ p3) ∧ ((((False ∨ p5) ∨ p5) ∧ p2) ∧ True)) ∨ True)) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148680124205982576848249009321 : ((((p5 ∨ (p2 → (p4 → p5))) ∨ (p4 → p2)) ∨ (p5 → (False ∨ (((False → p4) → (p1 ∧ p2)) ∨ False)))) ∨ (((p3 → True) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309966565932366523870897999997 : (p2 ∨ ((((p1 ∧ p4) ∨ p3) ∧ ((((p1 → (p5 ∧ False)) ∨ (True → (p1 ∨ False))) ∨ False) ∧ p4)) → ((False ∨ (p4 → (False → p1))) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208175170032862807359389598891 : (((p4 ∧ (p3 → True)) → (p1 ∧ p3)) → (((p4 → (((p4 ∧ p3) ∨ (p2 ∨ (True ∨ (True → (p2 → (p5 ∧ p4)))))) → p5)) ∧ p5) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148306521174516863086112276698 : ((((p5 ∨ False) ∨ ((p5 ∧ (p4 → (((False ∨ p4) → p3) → p3))) ∨ (p2 ∨ False))) → (False ∨ (True ∧ p4))) ∨ (p2 ∨ (False → (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_912932286176677043163889082962 : ((((((p3 ∧ p1) → (p4 ∨ p3)) ∨ ((p5 ∨ ((p4 → p2) ∧ p5)) ∨ ((True ∧ True) ∧ p4))) → ((p4 ∨ p5) ∧ ((p3 ∨ p3) ∧ False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∧ p1) → (p4 ∨ p3)) ∨ ((p5 ∨ ((p4 → p2) ∧ p5)) ∨ ((True ∧ True) ∧ p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162335372600210495204878244392 : (((((((((p5 → p5) ∧ (False → (True ∧ p2))) ∨ p1) → p4) ∧ p3) ∧ p4) ∨ p1) ∨ True) ∧ (True ∨ ((p2 ∧ False) ∨ ((True ∨ p4) ∧ p2)))) := by
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
theorem thm_5_vars_159008948294402857657656231968 : ((p4 ∨ ((p2 ∨ (((p2 ∧ p4) ∧ False) ∨ ((p3 ∨ True) ∧ (False → ((False → p3) → True))))) ∨ p4)) ∨ ((p4 ∨ True) ∨ (p3 ∧ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255667103616373413573489017798 : ((p5 ∧ p5) → (((p1 ∨ ((((p2 ∨ (False ∨ ((p4 → False) ∧ p2))) ∨ (False ∨ p5)) ∨ True) ∨ (False → p1))) ∧ (p1 ∨ (False → p3))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112693141484573693254722753748 : (((((p3 → (((p5 ∧ p4) → (((p3 ∨ (p2 → p5)) → p1) → True)) ∨ p3)) ∧ p4) ∨ (p5 → ((p1 ∧ True) → p5))) → p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616496038398979433491168078749 : (((((p4 ∧ (((p5 ∧ p5) → ((p5 ∧ (p2 ∧ p3)) ∧ p5)) ∧ p3)) → ((p4 → p1) ∧ ((((p5 ∧ p5) ∨ p2) ∨ p5) → p4))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348227545960723650450050360125 : (p3 → ((p4 → p4) → ((False → p2) → ((p5 ∧ (p2 ∨ ((((p5 ∨ (p3 ∨ False)) ∨ True) ∨ p5) ∧ p2))) → (((False ∨ p1) → p4) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h16 =>
            -- False on the left can always be used.
            apply False.elim h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192302600522340496027961679722 : (((True ∧ (True → ((p2 ∧ False) ∧ (p2 ∧ p5)))) ∧ p1) → (False ∧ ((p5 ∨ True) ∧ (((True → p5) → (((p4 → False) ∨ p2) → p4)) ∨ p2)))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h14.left
  let h17 := h14.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- We need to get the left conjuct of h19 based on <expert-advice>.
  let h20 := h19.left
  -- We need to get the right conjuct of h20 based on <expert-advice>.
  let h21 := h20.right
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178287302645782483492706702733 : (((p4 ∧ (False ∧ (((p5 → (p1 ∧ True)) ∧ p5) ∨ p3))) ∧ (p2 → False)) ∨ ((((p2 ∨ (p4 ∧ p2)) ∧ p3) → (p3 ∧ False)) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137843417380707049909223359544 : ((p3 ∨ (((False → (p1 ∧ p3)) → (False ∧ p5)) ∧ (((p4 ∧ ((p2 ∨ p5) ∧ (True ∨ p1))) ∧ False) → (p5 → p4)))) ∨ (False → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41373762421291603157672633487 : ((((p3 ∧ ((((p5 → False) ∨ True) ∧ ((True ∧ (p2 → p1)) → (True ∨ p1))) ∨ False)) → ((True ∧ ((p3 ∨ p2) ∧ p1)) ∨ p4)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112509070746200930183959783642 : (((((p4 ∧ ((p4 ∧ ((p2 → False) ∧ ((p1 ∨ p3) ∨ (True ∧ p3)))) ∧ (((p2 ∧ p3) → True) ∧ p3))) ∧ p3) → p5) → p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66410272853232384418913184292 : ((p5 ∨ (p2 → ((((p5 ∨ ((p3 → (p4 ∨ (p5 ∧ True))) ∨ p3)) ∨ (False ∧ (p3 ∧ p4))) ∧ (p1 ∧ ((p1 ∧ False) → p1))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252119166589958651849687272180 : ((p4 → p2) ∨ ((True ∨ False) → ((p3 → (p2 → False)) ∨ ((((p5 ∧ (p4 ∧ p3)) ∨ (p5 → (p2 → p3))) ∨ (True ∨ (False ∧ p5))) ∨ p1)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748906704757316549267359097282 : ((((p4 → p2) → ((p2 ∨ ((((p5 ∨ (p2 → p2)) ∧ (p1 ∨ ((p5 ∨ p4) ∧ p2))) ∧ p1) → p1)) ∧ (((p1 ∧ p1) ∧ True) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52578316640282925392758054771 : (((((p2 ∧ (p2 ∧ (True ∨ p2))) ∨ ((p3 ∧ p4) → p1)) → (p4 ∧ p4)) ∨ (p4 ∨ (False ∧ (p2 ∧ ((p4 ∧ (p2 → True)) ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345433415847713848883264594915 : (p3 → ((((((((p2 → (False ∧ (p1 ∨ p1))) ∨ False) ∨ (((False ∧ True) ∨ True) → p5)) → p4) ∨ False) → (False ∨ p5)) ∧ (p2 ∨ True)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219150869070703057835446202236 : ((True ∨ (p5 → (p5 ∨ p5))) → ((True → ((p1 → ((p4 ∧ (((p2 → False) → p1) → (p2 ∨ p2))) → (p5 ∨ (p5 ∧ p3)))) → p4)) ∨ True)) := by
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
theorem thm_5_vars_134251454754831288352642474435 : ((((p3 ∨ (p3 ∧ p3)) ∧ ((p1 ∨ (((p1 → p2) ∨ (p1 → p3)) ∧ (p3 ∨ p1))) ∧ ((True → p5) ∧ p5))) ∨ p3) ∨ (True ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722221858701054083217573208439 : ((((p5 → ((p4 → p5) → p1)) → ((p1 ∧ True) → (((p2 ∧ ((p4 → p5) → p2)) ∨ (p3 ∨ (p2 ∨ p2))) → (p5 ∧ (p3 → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178552835927699128984701415131 : ((((((p1 ∧ p4) ∨ p3) ∨ p5) ∨ p1) ∧ ((True ∨ True) ∧ (p4 ∧ p3))) ∨ ((True ∧ True) ∧ ((True → (p3 ∧ ((p4 ∧ p2) → True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



