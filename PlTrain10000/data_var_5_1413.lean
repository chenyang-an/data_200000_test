variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50351266293118356739819335172 : ((((p4 → ((False ∨ p1) ∨ p3)) ∧ (((True ∨ p2) → ((p5 ∨ (True ∨ p3)) ∨ True)) ∧ (p2 ∨ p1))) ∨ ((p1 → False) ∧ (p3 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80451155729280463257760960997 : ((((p5 ∧ (((True ∨ True) ∨ p1) ∨ p1)) → (p1 → ((p4 ∨ ((p3 ∨ (p3 ∧ p1)) → p5)) ∨ ((p1 ∧ p5) ∧ p1)))) → (p1 ∨ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∧ (((True ∨ True) ∨ p1) ∨ p1)) → (p1 → ((p4 ∨ ((p3 ∨ (p3 ∧ p1)) → p5)) ∨ ((p1 ∧ p5) ∧ p1)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h4
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h4
          -- One of the premise coincides with the conclusion.
          exact h5
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h11
        -- One of the premise coincides with the conclusion.
        exact h5
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h12
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233200574885491665736198599807 : ((p5 ∧ (True → p3)) → ((((True → (p2 ∧ ((((p4 → (p4 → ((p5 → p4) ∨ p3))) → p5) ∧ True) ∧ (False ∧ False)))) ∧ p5) ∨ True) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40563471354847998650888134557 : ((((p3 → (((((p5 → p4) ∨ (p3 ∧ p5)) ∨ p3) ∨ (p5 ∧ p1)) ∧ (((p1 ∨ p5) ∨ (p3 ∨ False)) ∧ (False ∨ p5)))) ∨ p4) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234136597943600476801151475651 : ((True → (p5 ∨ True)) → ((((True ∨ True) ∧ (False ∨ p4)) ∨ (((((p4 ∧ (p2 ∧ p2)) → p1) ∨ p4) ∧ p4) → (p2 ∨ p1))) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4391224928884752683925403806 : (p1 → ((False ∨ ((((False ∧ ((True → False) → True)) ∧ p3) ∧ (((p4 → (p3 ∧ p2)) ∧ (p4 → False)) ∧ (p3 ∨ True))) ∨ p1)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689026474365394888140027227744 : (((((((False ∧ (p2 ∨ False)) ∧ ((p4 ∧ p5) ∨ p2)) ∧ (p3 ∧ (p4 → False))) ∨ p2) ∨ ((((p2 ∨ (p2 ∧ False)) ∧ p4) ∧ False) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_706974262084397691732914466642 : ((((((p5 → p5) ∧ (p3 → (p4 ∨ p5))) ∨ p5) ∨ ((p3 ∧ p3) → (p5 → ((p2 ∨ p2) ∨ ((((p1 → p1) → False) → p2) ∨ p1))))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350174703191413658683370330937 : (p4 → ((((p1 ∨ (False ∧ False)) → (p5 ∨ p3)) → ((p5 ∧ ((p1 ∧ (p1 ∨ False)) ∧ (p2 ∧ (True ∨ (False ∨ p3))))) ∨ (p4 ∨ p2))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302630519216784027810771787720 : (False ∨ (p2 ∨ (((False ∧ p3) ∨ ((p1 → (p3 → (p2 ∨ (p1 ∧ ((p2 ∧ p3) → p1))))) ∧ ((p2 ∧ (True ∧ p3)) → p2))) ∨ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177736631737162570007327197953 : ((((p5 ∨ (p1 → p1)) ∧ (((True → True) ∧ p3) → (False ∨ False))) ∧ p3) ∨ ((((p1 → ((p5 → p5) → p4)) ∧ p1) ∧ (False ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151798305117791514255639461245 : ((((((p1 ∧ (p5 → p2)) → p4) ∨ (False ∧ (p4 → (True → p1)))) ∧ True) ∧ (p3 → (True ∧ (p3 ∨ p4)))) → (((False ∨ p2) ∧ False) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158980777771956549660601393034 : ((p3 ∨ ((p3 → (p4 → ((False ∧ p2) → (p4 ∧ ((p2 ∨ True) ∧ p2))))) → (p2 → (p1 ∨ p4)))) ∨ (False → ((p4 ∧ p2) ∧ (p4 ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42955585093702970035508932956 : (((p4 → (p1 → ((False ∨ (p2 → (((p1 ∧ ((((p2 ∧ False) ∧ (p1 ∨ True)) ∨ False) ∨ p5)) ∧ (True → p5)) → True))) → p2))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156969406245894600141671023477 : ((((((p3 ∧ False) ∨ (p2 → p3)) ∧ ((p4 ∧ True) ∨ p5)) ∨ (((p2 ∧ True) ∧ False) ∧ p2)) ∨ p5) ∨ (((p4 ∧ p2) ∧ True) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148313679367608084906695167785 : (((p5 ∧ ((p2 → (p5 → p5)) ∧ ((p1 ∨ (True ∨ ((False → p5) ∧ p5))) ∧ p5))) → (p4 ∨ (p1 ∨ p5))) ∨ (((p2 ∧ p5) → True) ∧ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68294159242329206501386244892 : ((p3 → ((p3 ∧ (p1 ∧ ((((p1 ∧ p1) → ((False → p3) ∨ ((True ∨ p2) ∨ p4))) → (p2 → p4)) ∨ p4))) ∨ ((p2 → p2) ∨ False))) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123020281447069655012399725043 : ((((p5 ∨ p4) → (p5 → ((p5 ∧ p3) ∧ ((p4 → (p3 → (((p4 ∨ p3) ∧ p5) → p4))) → True)))) ∨ ((p2 ∨ False) → True)) → (p3 → p3)) := by
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
theorem thm_5_vars_111182685758772016858762829078 : (((((p1 → (p4 → p3)) → p1) → (p2 ∨ (((p3 ∧ (p4 ∧ p5)) ∨ (p3 ∧ (False ∧ (p5 ∨ (p1 ∨ p2))))) ∧ p1))) ∧ p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178114183067864248497140162108 : (((((True ∧ p4) ∧ (p1 ∨ ((p1 ∨ p3) ∧ p4))) → (True ∨ p5)) → p3) ∨ ((p2 → (p1 ∧ (p1 → p1))) → ((p2 ∨ (True ∨ p1)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181402493841737194919559178014 : ((p2 ∨ ((((p1 → ((True ∨ p4) ∧ p1)) ∧ p3) → (p4 → p4)) ∨ False)) → ((((p1 → (False ∧ True)) ∧ (p4 → p5)) ∧ (p2 ∧ p1)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h15 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h16 := h5 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303268798554073141277843822750 : (False ∨ (p5 → (False ∨ (((((p2 → p5) ∨ (p2 → (p1 ∨ p5))) → p2) ∧ (p4 → ((False ∧ ((p5 ∨ p4) → p1)) → (p1 → p2)))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → p5) ∨ (p2 → (p1 ∨ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729825799255364634308107511211 : (((((True ∧ p4) → p4) → ((p4 → (((False ∨ (p1 ∨ (False ∨ ((False → p5) → p4)))) ∧ (p5 ∧ (p4 ∨ p5))) → (True ∧ p1))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166700533269750985278531146013 : ((p3 → ((False ∨ ((False ∨ False) ∨ (True ∧ (False ∧ ((p1 ∨ p1) ∨ (p5 ∨ p2)))))) ∧ p2)) ∨ ((p3 ∨ (p3 → True)) ∨ (p4 → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350040548450086404318824439378 : (p4 → ((((p3 → p4) ∨ (((((p2 ∧ p3) ∨ (((False → (p5 ∨ (False → True))) → p5) → (p5 ∧ p2))) ∧ p2) → p2) → p4)) → False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329118104802392979562120363147 : (True → (((p1 ∧ p2) ∨ (p1 ∨ False)) ∨ (p3 ∨ (((p5 ∨ p2) → (((p2 ∧ p3) ∨ p5) ∨ (p2 ∧ (True ∧ ((False → p2) ∨ p2))))) ∨ p2)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52517977839279322284273587725 : ((((p5 ∨ ((((p4 → (True ∨ p2)) ∨ (True ∧ p5)) ∧ p4) → p4)) ∧ p5) ∨ ((True ∧ p4) ∧ (p4 ∧ (((p3 → True) ∨ p4) ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_28192384239583467542359022729 : ((True ∧ ((p3 ∨ ((((p5 ∧ p1) → (p3 ∧ False)) → (p2 ∧ (p4 ∨ False))) ∧ ((p1 ∨ p5) ∨ (p2 → (p2 ∧ (True ∨ True)))))) ∨ True)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213077980581511325390817549668 : ((((p1 ∧ p4) ∧ p3) ∧ p5) ∨ ((True ∨ False) ∧ (p3 ∨ (((True ∨ (((p1 → p4) ∧ p3) ∨ (((p2 ∨ p5) ∧ p4) → p2))) ∨ False) → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672016786793673323690607712800 : ((((((((((p2 ∨ True) ∨ p1) ∨ (((p2 ∧ (False ∨ p3)) ∨ True) → p1)) → p4) ∨ p3) ∨ (False ∨ p5)) ∨ p4) → ((p1 → False) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_239599938598680158085191943385 : ((p3 ∨ True) ∧ ((p5 ∧ (((p3 → p2) ∨ p3) ∨ True)) ∨ ((((((p2 ∧ False) → (p4 ∧ (p3 → p3))) → p1) → p1) ∧ p5) → (p4 → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185344392228549422759720704916 : ((p4 ∧ ((p5 ∧ (False ∨ (p3 → (p1 ∧ (p4 ∨ p2))))) → p4)) ∨ (p2 → ((p1 → ((((p3 ∨ (p1 → p5)) ∧ p4) ∧ False) → p5)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346450119648891106091154183521 : (p3 → (((((p4 ∨ (p2 → p1)) ∨ p1) ∧ ((p2 ∧ (p5 ∧ (p1 ∧ p2))) → p1)) ∧ (p3 ∧ (p4 ∨ ((p3 → p3) ∨ p2)))) → (p1 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h4.left
      let h10 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h4.left
      let h17 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h4.left
    let h24 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207125855132114775100624026158 : (((p4 ∨ (p5 → (True ∨ False))) ∧ p5) → (((p3 ∨ (True → (False ∨ (p3 ∧ p2)))) ∨ (((p1 → p4) → (p4 ∨ True)) ∨ p2)) ∨ (p1 ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249977669361715531516299162927 : ((True → p2) ∨ ((((((p3 ∧ p5) ∧ (p5 → (p2 ∧ (p4 ∨ p4)))) ∧ p4) → True) → (p3 ∨ p4)) ∨ ((((p2 ∨ True) → p4) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706510512815647397382089786718 : ((((p5 ∨ (((False ∨ p5) ∨ p4) → (p4 ∨ p5))) ∧ (((p1 ∨ p5) → (p1 ∨ ((p3 ∧ p5) ∧ ((p3 ∨ p5) ∨ (False ∧ p5))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65133308160976289806930482509 : ((p2 ∨ (p1 → (p1 → (((((p3 ∧ (p5 ∨ (p2 ∧ p2))) ∨ p1) ∨ ((p3 ∨ False) → ((False → p2) ∨ (True ∨ True)))) ∨ False) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41550745175975222820749010172 : ((((p3 → ((False ∨ (p1 ∧ (p2 → p2))) → (p4 ∨ p5))) ∨ ((p1 ∧ ((((True ∨ p3) ∨ p3) → True) ∨ p2)) ∨ (p5 → p5))) ∨ p4) ∨ p4) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606704605142262336498428992940 : ((((((p3 → (p4 ∧ (True ∧ (p4 ∨ (((True ∧ ((False ∧ p5) ∨ (p3 ∧ False))) → p3) → (p2 ∧ p2)))))) ∧ (p1 → p5)) ∧ p3) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113099234374891170417411175846 : (((True → (((p5 → p4) → (p5 → (((p5 ∨ ((p1 ∧ (p5 ∨ p4)) → p1)) ∧ p4) ∧ (p5 ∨ (p1 → p1))))) ∧ p1)) → False) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159732856558086591059849496774 : (((((p3 ∨ p1) ∨ ((p3 ∨ p3) ∧ p2)) ∧ (((p2 ∧ True) ∧ ((p4 ∧ p2) ∨ True)) → False)) ∨ False) → ((p1 → (p3 ∧ (p1 → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
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
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186685452615315961123212130058 : (((True → (((p5 ∧ p1) ∨ True) ∧ True)) ∧ (True → (p1 ∧ False))) → ((p4 ∨ ((((True → False) → p1) → (False → True)) → (p1 ∧ True))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612593917024480837593201027918 : ((((((p5 → (p3 ∧ (p1 ∧ ((True ∨ (True ∧ True)) ∨ (p5 ∨ (((p2 → (False ∨ p2)) → False) ∧ True)))))) → p2) ∨ (p5 → p5)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_685141112792246753081545038135 : ((((p3 ∨ (((p2 ∧ ((((True ∨ False) ∧ p2) → True) ∧ (p4 → p2))) ∨ p5) ∧ (p3 ∧ p2))) ∨ ((False ∧ (p3 → (p5 → False))) → False)) ∨ False) ∧ True) := by
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
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328511733614185765331142761851 : (True → ((((((p2 → (p4 → True)) ∨ p2) ∨ p3) → ((p1 → (p5 ∨ False)) ∨ True)) ∨ True) ∨ (False → (p1 → (((True → p2) → False) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715161113361907721694636271135 : ((((True → ((p1 ∨ (p5 → True)) ∧ True)) → (p2 → ((True → p5) ∨ ((False → ((p4 ∧ ((True ∨ p5) → p1)) ∨ (p2 → p1))) ∨ p5)))) ∨ p1) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55197565336326235414706933875 : ((((False → (p5 → (False ∨ p1))) → p5) ∨ (((p3 ∨ (p1 ∨ (p1 ∨ ((True ∨ (p1 ∨ p1)) → False)))) → p5) ∧ (p1 → (p3 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115079145629245659123762807190 : (((p1 ∧ (((p3 ∨ ((True ∧ (p4 ∨ p2)) ∧ p3)) ∨ p3) → p4)) ∨ (((p4 → p2) ∨ (p5 ∨ True)) ∧ (p2 → (p2 ∨ p5)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41702935071730423215200553309 : (((((True ∨ p2) ∧ (p3 → (False ∧ p3))) → ((p5 → (p5 ∨ True)) → (p1 ∨ ((((p1 → (False ∧ True)) ∨ p5) ∨ True) ∧ True)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60572653372924588420959893291 : ((True ∧ (((True ∨ ((p2 → (((p4 → (True ∧ p4)) → (p5 → (((True → p3) ∨ p4) → p3))) → p1)) ∨ p4)) → (p2 → p1)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356516728118295682456389901176 : (p5 → ((p3 → ((((p4 ∨ p4) → (False → p4)) ∨ False) → True)) ∧ ((((False ∧ p5) ∧ (((p1 → (p5 ∧ p3)) ∧ p4) → p1)) ∧ p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158997862788188874653961654466 : ((p3 ∨ (p4 ∨ ((p1 ∧ (((p1 ∨ (p3 → p5)) ∧ True) → False)) ∨ (True ∧ (p1 → (True ∨ p4)))))) ∨ ((p1 → (p3 ∧ (p4 ∨ p2))) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65317806417892165661218057545 : ((p3 ∨ (((p2 → p5) ∨ (p3 ∧ (((p1 ∧ p3) ∨ (((False ∨ p4) ∧ ((p5 ∧ p1) ∧ True)) → False)) ∨ p1))) ∨ ((p4 ∨ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185126851329124169234387725429 : (((p1 ∧ p2) → (True → ((False ∨ (p1 ∧ (p4 ∧ False))) ∨ False))) ∨ ((((p3 ∨ ((False ∧ p4) → ((False ∨ p5) ∧ True))) → p3) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206302086566886213744629414052 : ((p1 ∨ (((p2 ∨ True) ∨ p1) → p1)) ∨ ((((((p2 ∧ (p2 → ((True ∨ p2) → p4))) ∨ p4) ∧ p4) → (p5 ∨ True)) ∨ p1) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134308256602277152680008461467 : (((True ∧ ((p2 ∧ (p1 ∨ ((p1 ∨ True) ∨ p3))) ∨ ((p3 ∨ (p1 → ((True ∨ (p1 → p3)) ∨ p1))) ∧ p3))) ∨ p2) ∨ (p3 ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591557862799011566846426716538 : (((((p5 ∨ ((p3 ∧ p3) ∨ (p2 ∧ ((p1 → (((p1 ∨ ((p5 → p5) ∧ (p3 → p4))) ∧ p5) ∨ p1)) ∧ p2)))) ∧ (p4 ∨ p2)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215950264833766909105152601836 : ((p4 ∨ ((p3 ∨ p2) ∧ p5)) ∨ ((p5 → (False ∨ ((p5 ∧ ((p3 → (((True ∧ p4) ∧ (p5 ∨ p5)) → p5)) ∨ (p4 ∨ True))) ∧ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43990692890279619305505238268 : ((((((p3 ∨ False) → (((p1 ∨ p2) → ((p1 ∧ (p1 → (p3 ∧ ((p5 → p4) → False)))) → p5)) → p1)) ∨ False) → (p5 → p1)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802576326062225972240645131204 : (((p2 → (p5 ∨ (((((p4 ∨ p5) ∨ True) → (((p2 ∨ ((False → p4) ∧ (p4 → (p5 ∧ False)))) → (p3 ∧ p5)) → p1)) ∨ True) ∨ p3))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65337038625707629361713703095 : ((p3 ∨ (((((p3 ∧ ((True ∨ p3) ∧ True)) ∧ p3) ∨ p1) ∨ (((p5 → (p3 ∧ p2)) ∧ True) ∧ True)) → (True → (p3 ∧ (p4 → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184711490185998795903392484773 : ((((p1 → p3) ∧ (p4 → (p5 ∨ p1))) → (p2 ∧ (False ∧ p5))) ∨ ((p4 → (p3 → (p1 ∨ (p1 ∨ p1)))) ∨ (((p3 → True) ∨ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809061493557477865985196510902 : (((p5 → ((p5 ∧ ((True ∨ p2) → ((p1 ∧ (p5 → (((False ∧ (p5 ∧ p5)) ∨ (True → (p4 → p3))) ∧ (p3 ∨ p3)))) → p4))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38182546776022205229681754949 : ((((p5 ∧ ((p2 ∧ ((p5 ∧ (p3 ∧ p5)) ∧ (p1 ∨ (False ∧ p4)))) ∨ (p2 ∨ ((p3 → p4) → p4)))) ∨ ((False ∨ p4) ∨ p1)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162355561414566586178986454568 : ((((True → ((False ∨ p3) ∧ (p5 ∨ (True ∧ ((p2 → p3) ∧ (p2 ∨ p4)))))) ∨ False) ∨ True) ∧ ((False ∧ (p4 ∨ ((True ∨ p3) ∧ p4))) → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755022685404489561662029046942 : (((False ∧ (True → ((p2 ∧ (False ∨ (True → p1))) → ((p5 ∧ p4) ∧ (p3 → ((p4 ∧ ((p5 ∧ p2) ∧ (p2 → p4))) ∧ (p3 ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157276511066024288314985841700 : ((((p2 ∧ (p2 ∨ p3)) → (p2 ∧ (((p4 ∧ ((p5 → p1) ∨ p1)) ∧ (p4 ∨ True)) → p1))) → p2) ∨ (False → ((p4 → True) → (p2 ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157327578481213104271186367635 : (((True ∨ ((((p5 → ((False → p1) ∧ p3)) ∧ p4) → p5) → ((p5 → True) ∨ (p1 ∨ p3)))) → p5) ∨ (p5 → (p1 ∨ (p5 ∧ (p5 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198255347732037843663967834766 : ((False ∧ ((p5 ∧ (p3 ∧ (p3 ∨ p4))) ∧ p1)) ∨ ((True ∧ (True → ((True ∨ (True → (p1 ∧ (((p2 → False) → p1) ∧ p4)))) ∧ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159058721641873583123576575488 : ((p5 ∨ ((False → ((p3 → (p4 ∧ p5)) → p2)) ∧ (((p5 → p4) ∧ p5) → ((p2 ∧ False) ∧ p5)))) ∨ (p5 → (((p5 ∧ p1) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40415031997765932318074137147 : (((((((p4 → ((p2 → (p1 ∨ (p4 ∧ (p1 ∨ p2)))) ∧ p2)) ∨ (True ∨ p5)) ∨ p5) → ((p5 → p3) ∧ (True → False))) ∨ p3) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310389025251900001412142523360 : (p2 ∨ ((((p3 ∧ True) ∧ (p5 ∨ (p2 ∧ p1))) → p4) ∨ ((((p3 ∨ (p4 ∨ p1)) ∨ p3) ∨ p5) ∨ (((p3 ∧ False) → p3) ∨ (p2 ∨ p1))))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260670077020189529285356898918 : ((p3 → p3) → ((((True ∨ (p4 ∧ ((p1 ∧ p5) ∧ True))) → False) ∨ p2) ∨ (((True ∨ ((p2 ∨ (False ∨ p3)) ∧ p2)) ∨ p2) → (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149953166116411632302042536220 : ((p4 ∨ (((((p4 ∧ p2) ∧ ((p3 ∧ True) ∨ False)) → ((p3 ∨ p1) ∧ ((p4 ∧ False) ∧ True))) → p4) ∧ True)) ∨ (p1 ∨ ((False ∨ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190969065136425949149112165749 : (((((False ∨ False) ∧ p3) ∧ p3) ∨ (False ∧ (True → p5))) ∨ (((p3 → p3) ∨ p4) ∨ ((True ∨ (p4 → False)) → (False ∧ ((True → True) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42363736146127215849221749004 : (((p3 ∧ (p5 ∨ ((((p3 ∨ True) ∧ p4) → p5) ∧ (p3 → ((p4 → (p4 → ((False ∧ ((p5 → p2) ∨ True)) ∧ True))) → p1))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148114344269468986485986993793 : ((((p3 ∨ (((True ∨ True) ∧ p5) ∨ (p3 ∧ False))) ∨ ((p4 → True) ∧ (p3 ∨ (True ∧ p5)))) → (p1 ∧ p3)) ∨ (False → ((p1 → False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119151460471128823589441564712 : ((p2 → ((((p4 ∧ p3) ∨ (p5 ∨ ((((p5 ∨ (p4 ∧ p5)) → ((p5 → False) ∨ (p3 ∨ p1))) ∨ False) ∧ p1))) ∧ True) ∧ False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64056300791688984563800088353 : ((False ∨ (((True ∧ ((p1 → ((p1 ∨ p3) ∧ (((p1 ∧ True) → (p3 ∧ p2)) ∧ True))) ∧ p3)) → p5) ∨ (((False → p5) ∨ p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137252665050488503178304108243 : ((p1 ∧ ((True ∧ (p4 ∨ p4)) ∧ (p2 ∨ ((True ∧ (((p4 → (p3 → p1)) ∨ p1) ∨ p5)) ∨ ((p3 ∧ False) → False))))) ∨ ((True ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695658789866061060572080337797 : (((((True ∨ ((p1 ∨ (p1 → p4)) → False)) → (p4 ∨ (p4 → (p3 ∧ False)))) → (False ∧ ((((True ∧ p4) → True) → (p1 → p3)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137543545393611503591000527972 : ((p5 ∧ (p5 → (p1 ∧ (False ∨ (((((False ∧ p1) ∨ (((True ∧ p5) ∨ p1) → (True ∨ p5))) → p3) ∨ False) ∨ p2))))) ∨ (p5 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_821430247974400840882540233177 : (((((True ∧ (((((p4 ∧ p5) ∧ p3) ∨ (False ∧ p2)) → (p4 ∧ p5)) → p3)) ∧ ((p1 ∨ (p3 ∧ p5)) → ((p1 ∧ p1) ∧ True))) ∧ p2) → p3) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((((p4 ∧ p5) ∧ p3) ∨ (False ∧ p2)) → (p4 ∧ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- False on the left can always be used.
      apply False.elim h24
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h26 := h7 h8
  -- One of the premise coincides with the conclusion.
  exact h26
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227817118775434576662292197011 : ((p2 ∧ (p1 ∧ False)) ∨ (((p1 → (((True → (p5 ∨ p3)) → True) → True)) ∧ (p4 ∧ (p4 ∨ True))) ∨ (p3 ∨ ((p4 ∨ True) ∨ (p1 → True))))) := by
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
theorem thm_5_vars_147675412031016568431311012535 : ((((p5 → (p3 ∧ ((p4 → ((False ∧ p2) ∧ p1)) → ((p2 → p4) → (p5 → False))))) → (p5 → p3)) → p3) ∨ (True ∨ (p5 → (p3 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741472344679004095252986906330 : ((((p5 ∨ p2) ∨ (((p4 → p3) ∨ (p4 ∨ (p5 ∧ p1))) ∧ (True ∨ ((p3 ∨ p4) ∨ (p2 ∨ ((p5 ∧ p2) ∨ (p2 ∧ (False ∨ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305792548090420258763722707766 : (p1 ∨ (((p5 ∨ (True ∨ ((p4 → False) → False))) ∧ p5) → (((False ∨ (((((p3 ∨ p2) ∧ p2) ∨ (True → True)) ∨ p2) ∧ p2)) ∨ p5) ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113005841226374912059990293562 : (((p4 ∧ (((True ∨ p1) ∨ p1) ∧ ((((p2 ∧ p3) ∧ ((p2 ∨ False) ∧ (p2 ∨ (p2 ∧ (p3 ∨ False))))) ∨ False) → p3))) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611720743607857618794663434502 : (((((p5 ∨ (p4 → (((((p1 → p3) → p1) ∨ (p2 ∧ ((p2 → p1) ∨ ((p5 → p5) ∨ p2)))) ∨ (p4 ∧ p2)) ∨ p1))) → p5) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174224207177034098961999073882 : (((((p4 → p3) ∧ p1) ∧ ((True ∧ p2) → (p4 ∧ (p4 ∧ p4)))) → (p1 → False)) → (((p2 → (p3 → p1)) ∨ (p2 ∨ (p2 ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135792798020156246853772103142 : ((((p5 ∨ (p2 ∧ True)) ∨ ((True ∨ True) ∧ (p4 ∧ (True → (p3 ∨ p3))))) → (p3 → ((p1 ∨ p5) ∨ (True ∨ True)))) ∨ (p1 ∧ (p5 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
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
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h10.left
      let h16 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58165562701511800459982651839 : (((p3 ∧ False) ∧ ((((True → p4) ∧ (((p5 → (p4 ∨ p3)) ∧ p3) ∧ p1)) ∨ (p2 ∧ (True → p3))) ∧ (p5 ∧ (p2 ∧ (False ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779759449035496058529248573753 : (((p2 ∨ (((p1 ∨ ((((((p3 ∧ p1) ∨ p4) ∨ p2) ∨ p5) → (p1 ∨ False)) ∨ p3)) → ((p1 ∨ p4) ∧ ((p2 ∨ p3) ∨ p4))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745996357908719865370458414694 : ((((False ∨ p5) → (((p2 ∧ ((False ∨ p1) ∨ ((p4 → p1) ∨ p3))) → (p3 ∧ p4)) ∨ (p3 ∨ (p4 ∧ ((True ∧ p4) → (p1 ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56504728864428774786585869245 : (((p2 ∧ (False → (False ∧ p3))) → (((p5 → p4) ∧ ((p4 ∨ (p4 → ((False → (p1 ∧ (p3 → p1))) → p5))) ∨ (p2 → p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245344318016151361489457162306 : ((p2 ∧ p3) ∨ ((((p1 ∧ p4) ∧ p4) ∧ (False ∧ (((True ∨ p1) → False) → (True ∨ (p5 ∧ ((False ∧ (p1 ∧ (p5 ∨ p5))) ∧ p5)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111957226213917199476287497027 : ((((p5 ∧ (((p5 ∨ (p4 → False)) ∧ p3) ∨ p3)) ∨ (p4 → (((False → (p1 ∨ (p4 → True))) ∧ True) ∨ (p5 ∨ p4)))) ∨ True) ∨ (p5 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65430911157630618246550632141 : ((p3 ∨ ((False ∧ p2) ∧ (((((p5 ∧ (p2 → (False → (p4 ∨ (p3 ∧ False))))) → p1) ∧ (p4 ∨ True)) ∨ False) ∨ ((False → p4) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66713644358204509155174337597 : ((True → ((False → p3) ∧ ((((p4 → (p1 ∧ p2)) ∧ (False ∧ (p3 → (p3 → ((p4 → p4) → (p4 ∧ (p1 ∧ p3))))))) → p3) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166985658762566745193182839927 : (((p1 ∨ (((p1 ∨ p2) ∧ (True → ((p1 ∨ p1) ∧ False))) ∨ ((p3 ∨ True) ∧ p1))) ∧ p4) → (((p2 ∧ p1) → (p5 ∧ False)) ∨ (True ∨ p2))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



