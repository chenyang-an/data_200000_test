variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134544086772469917907372235713 : (((((p1 → (p5 ∧ ((((False ∨ p1) ∨ p4) ∨ True) ∨ p5))) → ((p5 ∨ p4) ∧ ((p1 ∨ p5) → p2))) → p3) → p5) ∨ (True ∨ (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316639563089745834054028465098 : (p3 ∨ (p4 ∨ ((p5 ∧ (p4 ∧ p2)) ∨ ((p5 ∨ (((((p5 ∨ (p1 ∧ True)) → (p4 ∨ p5)) → p2) → True) → ((p3 ∧ p5) → False))) → True)))) := by
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
theorem thm_5_vars_55694741765351345860192603635 : (((((p2 → p5) → p5) ∨ p5) ∧ (((p3 ∨ (p5 ∨ False)) ∨ ((p4 → False) → p4)) ∨ (((p4 → (p2 → p4)) → (False ∨ p4)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190885854217296493078941389083 : ((((p3 ∨ p4) → ((p2 ∨ p1) ∧ True)) → (p1 ∧ False)) ∨ (p2 ∨ (True ∧ ((((p2 → p4) → p1) ∨ (p4 ∧ ((True ∨ p3) ∧ p3))) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319048862822576634992085838668 : (p4 ∨ (((p2 ∨ ((True ∧ p4) → p5)) ∧ ((p4 ∨ ((p2 ∨ (p1 → ((p4 ∨ p4) ∧ False))) → p1)) ∨ False)) ∨ ((p2 ∧ p3) ∨ (True → True)))) := by
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
theorem thm_5_vars_133663842570643951755786015608 : ((((p2 ∨ ((p1 ∨ ((((p1 ∨ (True → (p2 ∧ p2))) ∨ p3) → False) ∨ (False ∧ p5))) ∨ True)) ∨ (p2 ∨ True)) ∧ True) ∨ ((True → p1) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_595404564618795870984046742055 : (((((p5 → ((p4 → (((p3 → p1) ∧ p1) ∨ (True ∨ p3))) → p4)) ∧ ((p1 ∨ ((False ∧ (p2 ∨ p2)) ∧ (False ∧ p5))) → True)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347420617286961988251505239479 : (p3 → ((p3 ∧ ((p5 ∧ ((p5 ∨ p4) ∨ p5)) ∨ p2)) → (((((p1 ∧ ((False → False) ∨ p1)) ∧ (p4 → False)) ∧ (p3 ∧ p4)) ∨ True) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h2.left
  let h14 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h22 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135286263806724085958197971714 : (((p3 → ((True → (((((True → p4) → (((p4 → p3) ∨ p2) → False)) ∧ False) ∨ p2) ∧ p1)) → True)) → (p4 ∧ p3)) ∨ (True ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110736092514757748685080130281 : ((((((p1 ∧ ((p2 ∧ p1) → p5)) → (p1 ∨ p2)) → ((((p2 → p1) ∨ ((p3 → False) → False)) ∨ p4) ∨ p2)) ∧ p2) ∧ False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357853608363946910505782339425 : (p5 → (p5 ∧ ((((p5 ∧ (p2 ∨ p2)) → p1) → ((((((p1 → (p1 → True)) ∨ False) → ((p3 ∧ p3) ∨ p4)) ∨ True) ∨ False) ∧ True)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_191813823652088802237247195084 : ((p2 ∨ (p1 ∧ ((True → p3) ∧ (p4 ∨ (p2 ∨ p3))))) ∨ ((p5 ∧ ((p5 → p1) ∨ ((p1 → p5) ∨ True))) ∨ ((p2 ∨ (False ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184956235174089701548052758159 : ((((p1 ∧ p2) → False) → (p1 ∨ (((p1 ∨ p5) ∨ p4) → p5))) ∨ ((((p4 ∧ (p1 → p1)) → (p1 ∨ False)) ∧ (p3 ∧ (p5 → p5))) → p3)) := by
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
theorem thm_5_vars_301134132324999050289623591246 : (False ∨ (((((p1 → p2) → (p5 ∨ p2)) ∧ p4) ∧ p2) ∨ (((p5 ∧ p5) ∨ (False ∨ (True → ((p2 ∧ (p3 ∧ p2)) → p1)))) → (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689542195602843503674515715114 : (((((p3 ∧ (((False ∨ True) → p1) ∨ (p5 ∨ False))) ∨ (p3 ∨ ((p1 → p3) → p3))) ∨ (((p3 ∧ p2) ∨ (p3 ∨ (p5 → True))) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586320025541471418487101585928 : (((((((p1 ∧ ((p3 → p1) ∨ p3)) ∧ p3) ∧ ((p5 ∧ True) → ((p3 ∧ False) ∨ (p5 ∧ ((p3 ∨ (False ∧ p3)) ∧ p5))))) ∧ p4) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329748613645174733271483361392 : (True → (True ∧ (((p2 ∨ ((True ∧ False) ∨ (((False ∧ (p5 ∨ (p4 → p4))) ∨ ((True ∨ (p1 ∨ True)) ∧ (p5 ∨ p5))) ∧ p1))) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60248684938107648220829193789 : (((False → True) → (p2 ∨ (True → (p1 ∨ ((((((((False ∨ False) ∨ p2) → p5) ∧ (p1 → True)) ∨ p2) → (p1 ∨ p1)) ∨ p1) ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148512555169435392234789849591 : (((((p3 ∨ (p3 ∨ True)) ∧ (((True → p2) → p1) → p1)) ∧ p2) → (p3 → (((p3 ∧ p4) ∨ True) ∧ False))) ∨ ((p2 → True) ∧ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692471832492560479318885285444 : (((((p1 → (((((p2 → True) → p5) → p5) ∧ p1) ∨ p4)) ∧ (p3 ∨ p1)) ∧ ((p2 → (p1 ∧ False)) ∧ (p5 ∧ ((False ∧ p1) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65257415581326673696943314563 : ((p3 ∨ (((p4 ∨ ((False → p5) → p1)) ∧ (p3 ∧ (((((p2 ∨ True) → ((False ∧ True) ∨ p3)) ∧ (True ∨ p1)) → p5) ∧ p3))) → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (((p2 ∨ True) → ((False ∧ True) ∨ p3)) ∧ (True ∨ p1)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h13 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h3.left
    let h16 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : (((p2 ∨ True) → ((False ∧ True) ∨ p3)) ∧ (True ∨ p1)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h20
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h23 := h17 h19
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38303740146483433827014642903 : ((((((((((p2 → ((p3 → (p4 ∧ p3)) ∧ p3)) ∧ p3) → False) ∧ p3) → p2) → p5) → p1) → (((True ∧ p5) ∨ p5) → p1)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301047394825711485996414133364 : (False ∨ (((p5 ∨ ((p3 ∨ (True ∨ False)) ∧ (False ∧ p1))) ∨ p1) ∨ ((p4 ∧ (((False ∧ p5) ∨ p5) ∧ ((p4 → True) ∨ p1))) → (p5 ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721809207419197257697155205128 : ((((p3 ∨ ((p2 ∧ p2) ∧ p5)) → ((((((p2 ∧ ((p4 ∨ p1) → p5)) ∧ (False → p2)) → p1) ∨ (p2 → p4)) ∧ (p5 ∨ p2)) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348025606723570718622280460773 : (p3 → ((p3 ∧ p5) ∨ ((p3 ∧ ((((p3 ∨ p2) ∨ p2) ∨ True) → (True ∧ ((p2 → (((False → p3) ∨ p2) ∧ p5)) → p2)))) ∨ (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305170371009380039664764605218 : (p1 ∨ ((((((p3 ∧ p1) → False) ∧ p3) → (p1 → (((p2 ∧ p3) ∧ (p5 ∧ p3)) → p3))) → (p5 → False)) ∨ ((p1 ∧ p5) → (p5 ∧ p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140420558674933485306426237274 : ((((False ∨ (((p1 ∧ ((p5 → ((True → p3) → True)) ∨ p4)) ∧ p4) ∧ (False ∨ p3))) → p5) → (p5 ∨ (p2 ∧ p3))) → (p3 ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68637178357006982620456399295 : ((p4 → (((((True → ((True ∧ p5) → ((True → False) → p4))) ∧ ((True → False) → (p1 ∧ p2))) ∨ (p1 → (p2 ∧ p5))) ∧ p5) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135219969908144428103987084653 : ((((((p5 ∧ (p4 → (True ∨ p2))) ∨ (p5 ∧ p3)) → p3) ∧ (((p3 ∨ p3) ∨ p1) → (True → p1))) → (p2 ∨ p1)) ∨ (False → (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200234512514271989877897008680 : ((((p4 ∨ p5) ∨ p1) → (p1 → (p4 ∧ p5))) → ((((((p1 ∨ (False → True)) → (True → p4)) ∧ p5) ∨ False) ∧ True) ∨ (False → (False ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725011009558047847458688337991 : ((((True → (p3 → False)) ∧ ((p3 → (((p1 → ((p2 ∨ (False ∧ (p4 ∧ (p3 ∨ ((p3 ∧ p2) ∨ p3))))) ∧ p3)) → False) ∧ p1)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248342053143313356774836835920 : ((p2 ∨ p3) ∨ (((False ∧ ((p5 ∨ (p2 ∨ p1)) ∧ True)) ∨ (p4 ∧ p4)) ∨ (((False → ((p2 → p2) ∧ False)) ∨ (True ∨ p4)) ∨ (p3 ∧ p2)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123021093420420582645240504841 : ((((p3 → p3) → ((False → (((p1 ∨ True) → (p1 ∧ p2)) ∧ (((p3 ∧ p3) → True) ∧ p1))) ∧ p3)) ∨ (False ∧ (False ∧ p4))) → (p3 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710540130275482272489936930648 : ((((((p5 ∧ False) ∧ p3) ∧ (p3 → True)) ∧ (((False ∧ (((True ∧ True) → p3) → p4)) ∨ (p5 ∧ ((p3 ∧ p1) → (p2 → p4)))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655556047277429914773684513560 : ((((((False ∧ (p1 ∨ (p1 → (((p2 ∨ False) → (p3 ∧ True)) → p5)))) → ((p5 ∧ (False ∨ True)) ∨ True)) → (p4 → p5)) ∨ (False → p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718656819810669705947936360560 : (((((p2 ∨ p1) ∧ (p3 → p5)) ∨ (p3 ∧ ((p3 ∧ ((p2 ∧ (((p4 → (p5 ∧ p3)) ∨ (False → p3)) ∧ True)) ∨ p3)) ∧ (False → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192158378507099485928959833439 : ((((((p2 ∧ p3) ∨ p4) ∨ (True → True)) ∧ p1) ∧ True) → (p5 → ((((p5 → (p2 ∧ (True ∨ (p3 ∨ p5)))) → p4) → False) ∨ (False → p5)))) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18778760031897913953835747286 : ((((((p2 ∨ (p1 ∧ ((((p2 ∨ (p1 → p1)) ∧ True) → p3) ∨ False))) ∧ True) → p3) → False) ∨ ((True ∧ False) ∨ (True ∨ (p2 ∨ True)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_671490948211640048374309459690 : ((((p3 → (((p2 ∧ True) ∨ (((p4 ∨ p5) ∧ p3) ∨ ((((p2 ∧ p4) ∨ p5) ∧ p1) ∧ (p2 ∧ p4)))) ∨ p1)) ∨ ((p5 → False) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_104803383738272650665398096574 : (((((((p5 ∨ True) ∧ (((p1 → p3) → p4) ∧ (True → (p1 → p5)))) → p5) → p5) → ((p1 ∨ True) → p4)) → (p4 → p4)) ∧ (False → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151836678701007290264679847386 : ((((((((p2 → False) ∧ False) ∨ (p1 ∨ p1)) → (True ∨ p2)) ∨ p1) ∧ p1) ∨ ((False → p1) ∨ (p2 ∧ p2))) → ((p4 ∨ (False ∨ True)) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248658871942832703652138323572 : ((p3 ∨ p1) ∨ (True ∧ ((p5 ∨ ((p4 → ((p4 ∧ p1) ∨ (((((p2 → False) → True) ∧ (p3 ∨ False)) ∧ False) ∧ True))) → p4)) ∨ (True ∨ p2)))) := by
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
theorem thm_5_vars_219552539014416457418919222372 : ((True → ((False ∨ p1) ∧ False)) → (True → (True ∧ (((p5 ∧ (p3 ∨ p1)) ∨ True) → (p2 ∨ (p4 → ((p3 ∧ p4) → ((True → True) ∧ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206038466104489000190388092523 : ((p2 ∧ (p1 ∧ (p5 → (p1 → p5)))) ∨ (((((p1 ∨ p4) ∧ (p3 ∧ p1)) ∧ (p4 ∧ False)) ∨ (True → (p5 ∧ p5))) → ((p5 ∨ p4) ∨ p1))) := by
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
      let h10 := h4.left
      let h11 := h4.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h6.left
      let h14 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h4.left
      let h16 := h4.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- We need to get the left conjuct of h19 based on <expert-advice>.
    let h20 := h19.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201183906427560219625591080553 : ((p1 → ((p1 ∨ (p4 ∧ p4)) ∨ (p3 ∨ p5))) → (((p2 ∧ (True ∧ p1)) ∨ (True ∧ (p4 ∧ (False ∨ p5)))) → ((p2 ∨ (p3 → p2)) ∨ True))) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350116456718536596021051004003 : (p4 → ((((False ∨ p1) → (p1 ∧ (True → ((((p1 ∨ p3) ∨ (p4 → True)) ∧ (True ∨ True)) → p3)))) → (p1 ∨ ((p1 ∧ p1) ∧ True))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45794571758478277389916005031 : (((p1 → ((True ∨ (((True ∨ (((False ∧ p4) → False) → True)) → p2) ∧ (False ∨ p2))) → (p1 ∧ (p1 → ((p5 ∨ p1) → True))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166203867391988553000322957707 : ((p1 ∧ (p4 ∧ (((p4 → ((p4 ∧ False) ∨ (p5 ∧ (p5 ∨ p1)))) ∨ (p5 ∧ p4)) → p5))) ∨ (p3 ∨ ((p1 ∨ ((p3 ∧ True) → p3)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40494215166965420159886832641 : (((((p2 → True) → ((((p1 ∧ ((p4 ∨ p3) ∧ (p5 → (True → p4)))) → p5) ∧ (False → ((False ∧ p4) → p5))) ∨ p5)) ∨ False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304684920458343246301825254539 : (p1 ∨ (((((p1 → (((((p5 ∧ (p3 ∨ (False ∨ p3))) ∧ p1) ∨ p2) ∨ False) ∨ p3)) ∧ (p3 ∧ (p4 → p4))) ∨ p5) ∨ p4) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716813235150076332276562942584 : ((((False ∧ ((False → p3) → p3)) ∧ ((((p2 ∨ ((((p1 ∧ (p5 ∧ (p2 → False))) ∧ p2) → True) ∧ p4)) ∨ p3) → p1) → (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43783561394308134569589547721 : ((((p1 ∨ (p4 → (p2 ∨ ((p3 ∨ (p2 ∨ p4)) ∧ ((((p5 ∧ False) ∧ p5) ∧ ((p5 ∨ (p4 ∨ False)) → False)) → p1))))) → False) → p2) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p4 → (p2 ∨ ((p3 ∨ (p2 ∨ p4)) ∧ ((((p5 ∧ False) ∧ p5) ∧ ((p5 ∨ (p4 ∨ False)) → False)) → p1))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49842228338893835256956337605 : ((((((True → ((True → (p4 ∧ (p3 → p1))) → (((p3 ∨ p1) ∧ p2) → p1))) ∨ p2) ∧ True) ∧ p5) ∧ ((p3 ∧ (p2 ∨ p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666277494356960160349381186928 : ((((((p4 → (p3 ∧ p5)) ∨ (((((p2 → (p4 ∧ (True ∧ True))) ∨ p5) ∨ p1) → p1) ∧ True)) → (False ∨ False)) ∧ (True ∧ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634125367728456612941849215642 : ((((((((p1 → p1) → False) ∨ p3) → ((p3 ∨ (((p1 → (p1 ∧ p5)) ∧ p2) ∧ (p2 ∨ p2))) → (p2 ∨ False))) → (p4 ∨ p3)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1955157150114032204645157857 : (((((True → p2) ∨ ((p1 ∨ p1) → (False → ((True → p1) ∨ p2)))) → p1) → (False ∨ (p1 ∧ p3))) ∨ (((p3 → p3) ∨ p4) ∨ p3)) := by
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
theorem thm_5_vars_47509678616767021367803364029 : (((p2 ∨ (((p3 ∨ (((p2 ∧ (p4 ∨ p5)) → False) ∧ ((p2 ∨ p1) ∧ p2))) ∧ False) ∧ (p4 ∧ ((False → False) ∨ p4)))) ∨ (p1 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135722534135991598324679314624 : (((((False ∧ (p3 → ((p5 ∨ (True ∨ True)) → (True → False)))) ∧ p4) ∧ True) ∨ ((p1 → (True → True)) → (p1 → True))) ∨ ((p4 → p5) ∧ p4)) := by
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
theorem thm_5_vars_211733314136447537851891508925 : ((True ∧ (p5 ∨ (p3 ∨ True))) ∧ ((p1 ∧ (False ∧ ((False ∨ (False ∧ p1)) ∧ ((p2 ∨ p4) ∧ p1)))) ∨ ((p4 ∧ (False ∧ p5)) → (p2 ∧ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137815497128094110260186577800 : ((p3 ∨ ((((p3 ∨ p5) ∨ ((p3 → (((p2 ∨ True) ∧ (p1 ∨ p5)) → (False ∨ False))) ∧ (False ∨ True))) ∨ p3) ∨ p4)) ∨ ((True ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343803746598426554187316205423 : (p2 → (p2 ∧ ((p1 ∨ (False ∧ ((p5 ∧ (p2 → (p3 → p4))) → (((False ∨ p3) ∧ (((True → p5) ∧ p2) ∧ True)) ∨ (p1 ∨ p3))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340828332206966353681099897725 : (p2 → (((p3 → (False ∧ (p2 ∧ (((((False ∧ (p4 ∨ False)) → p3) ∧ ((p2 → False) ∧ p4)) ∧ p1) ∨ (True → True))))) ∨ (p1 → False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732048701947424612219657289185 : ((((True ∧ p1) ∧ (((((((p4 ∧ p2) ∧ (p5 ∧ (p1 ∨ (p5 → p3)))) ∧ True) ∨ False) ∨ (p5 → p5)) → ((p5 → p2) → False)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133859377553933047079521182412 : (((p1 ∧ (p4 ∧ (((((p1 ∨ ((p1 → p4) ∨ p4)) → p5) ∧ (p4 ∨ p5)) → ((p5 ∨ p1) ∧ p3)) ∧ p3))) ∧ p4) ∨ (False → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_962264237950759451198193130995 : ((((p5 ∨ p3) ∧ (p3 ∧ ((((False ∨ (p1 ∨ (True ∧ True))) → p5) → p3) → ((p4 ∨ (p2 ∨ (p5 → ((p2 ∧ p2) ∨ p5)))) → False)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((False ∨ (p1 ∨ (True ∧ True))) → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (p4 ∨ (p2 ∨ (p5 → ((p2 ∧ p2) ∨ p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (((False ∨ (p1 ∨ (True ∧ True))) → p5) → p3) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h16
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : (p4 ∨ (p2 ∨ (p5 → ((p2 ∧ p2) ∨ p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h19
    -- False on the left can always be used.
    apply False.elim h21
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52349001082964562204677230502 : ((((p2 ∨ ((((p2 → p1) ∧ ((p1 ∨ p4) ∨ True)) ∧ p4) ∨ p3)) → False) ∧ (((p4 → p3) ∧ p1) → ((p2 ∧ (p2 ∧ True)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158987145355443718148650288231 : ((p3 ∨ (((p2 ∨ False) ∨ p4) ∨ (((True → p3) ∨ (p4 → True)) ∨ (True ∧ ((p4 ∧ p2) ∨ p3))))) ∨ (p4 → ((p2 → (p2 → p1)) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662330856802810758277286886818 : (((((((True ∨ p4) → True) ∧ ((False ∨ True) → False)) ∧ (p5 ∨ (False → ((p1 ∨ ((p4 → (p2 ∨ p5)) ∨ p3)) ∧ p2)))) → (p5 → p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h7 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218647705833683568939753098152 : ((True ∧ ((p5 ∧ False) → p4)) → (((p2 ∧ (p2 ∨ p4)) ∧ p4) ∨ (p3 → ((False ∧ (p3 ∨ True)) ∨ (((False ∨ (True ∨ p5)) ∨ p2) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_300147140583583340132249847508 : (False ∨ ((False ∨ ((True ∧ (p5 ∨ ((((p4 → p5) ∧ p2) ∨ ((p1 → (p3 ∨ p2)) ∨ (p3 ∧ (p3 ∧ False)))) ∨ False))) ∧ False)) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_947766827133485498576642748228 : (((((False ∨ p2) → (p3 ∨ p2)) → (((((p2 ∨ (False ∨ (p1 → p1))) → (p4 ∨ False)) ∨ p1) ∨ ((False → (False ∨ True)) ∨ p1)) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ p2) → (p3 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((((p2 ∨ (False ∨ (p1 → p1))) → (p4 ∨ False)) ∨ p1) ∨ ((False → (False ∨ True)) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720730564305408836054027576564 : (((((False ∧ (False → p4)) → p3) → (((p2 ∨ p5) → (p3 ∧ p1)) ∨ (p4 → (True ∨ (((p2 ∧ p3) ∧ True) ∨ (False → (p5 → p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148053938193873827110147828182 : (((p1 ∨ ((p3 → ((p3 ∧ (False ∧ (False ∨ (True ∨ p3)))) ∧ False)) ∧ ((p1 ∧ p4) ∨ p4))) ∨ (True → p2)) ∨ (p2 → (False → (p2 → p2)))) := by
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
theorem thm_5_vars_341992021077265121535880664571 : (p2 → (((True ∧ ((False → (p5 ∧ p4)) ∨ (True ∧ (p5 → True)))) → (((((p5 ∨ True) → p3) ∧ p3) ∨ False) → False)) ∨ ((p2 ∨ False) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19370586977376017276721866325 : ((((p4 ∨ (p4 ∧ (p5 ∧ p3))) ∨ ((p3 ∧ (False ∧ (True ∧ (p5 ∨ p2)))) ∨ True)) ∧ (((p1 → p5) → (p1 → p1)) ∧ (False → p4))) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50274699399622173348635894651 : (((((((p1 ∧ p1) ∨ p4) ∧ (p1 ∨ ((p2 ∧ p1) ∧ True))) ∧ (False ∨ (p4 ∧ p2))) ∨ (p3 ∧ p4)) ∨ (((False ∧ p4) ∨ p4) → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46905261847407251919384442042 : (((((((True → ((p1 → False) ∧ p3)) ∧ ((p1 ∨ ((p1 → p2) → p1)) → p2)) → p5) ∧ ((p2 ∧ False) ∧ p2)) ∨ p3) ∨ (False → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805436099244502285903778901802 : (((p3 → (p2 ∨ ((True ∧ (((p3 ∨ True) → True) ∧ ((p3 ∨ p4) ∧ ((p4 ∨ ((p5 ∧ False) ∨ (p4 ∨ (p1 ∧ p4)))) ∨ p3)))) ∨ p3))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118487536096161722656536769354 : ((p3 ∨ ((((p5 → p3) ∨ p2) → ((True → (((((p4 → p2) ∨ p1) ∨ False) → p2) ∧ p1)) ∨ True)) ∨ (p2 ∧ (p4 ∨ p1)))) ∨ (p1 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142991714720333137526508660229 : ((True → ((((p4 ∧ p5) ∧ (((p5 ∨ True) ∧ True) ∨ (p4 ∧ p2))) ∧ ((True → p4) → p1)) ∨ (p2 ∧ (p5 → p3)))) → ((p3 ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53907490888787278502672766810 : (((p5 ∧ ((p4 ∨ (p2 → (p5 → p2))) → (p5 ∧ p3))) ∨ ((((p1 ∧ p5) → (p5 ∨ (p3 ∨ (True → True)))) ∨ (p2 ∧ p4)) ∨ False)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174676134437360032358256918323 : (((p1 → (p5 ∨ True)) ∧ (((p2 ∨ (False → p1)) ∨ (p2 ∧ (False ∨ p2))) → p2)) → (((p2 → False) ∨ (p5 ∨ p4)) → (p2 ∨ (p5 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∨ (False → p1)) ∨ (p2 ∧ (False ∨ p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : ((p2 ∨ (False → p1)) ∨ (p2 ∧ (False ∨ p2))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h15 := h12 h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h1.left
      let h18 := h1.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : ((p2 ∨ (False → p1)) ∨ (p2 ∧ (False ∨ p2))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h19
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135882599789084677342249014063 : (((p4 ∧ (p2 ∨ (p5 ∧ ((False ∧ False) ∧ ((p3 ∧ p1) ∧ False))))) ∨ ((p3 ∧ p4) → (True → ((p2 ∧ p5) ∧ p3)))) ∨ ((p4 → p4) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228890034919739484209145397093 : ((p4 ∨ (p3 ∧ True)) ∨ ((p3 ∨ (((p3 ∧ ((p1 ∨ (p4 → p3)) → ((p5 ∨ ((p5 → (False → p5)) → p3)) → False))) → False) ∨ True)) ∧ True)) := by
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
theorem thm_5_vars_219783509737194318272578792736 : ((p2 → (p1 ∧ (p1 ∨ p5))) → ((p5 → (((p3 ∧ p1) ∧ (((p4 → p4) ∨ p3) → ((p3 → p5) ∧ False))) → p4)) ∨ ((True ∧ p5) → p3))) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 → p4) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646416031084513825320203188548 : ((((p1 → (((p3 ∧ p4) → (((p3 → (p1 ∧ True)) ∧ (p5 → True)) → ((p5 ∨ (p2 ∨ p3)) ∧ (False ∧ (p2 → True))))) ∧ p3)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179814189040449460705752511541 : (((True ∧ ((((p3 ∨ ((False ∨ True) → p1)) ∧ p5) → p4) ∧ p5)) ∧ True) → (((p1 ∧ p5) ∨ p3) ∨ (p5 → (True ∧ ((p4 ∧ p4) ∨ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164542940255198222678689356274 : ((((p3 → (p5 → ((p2 → p4) → (p2 ∧ p5)))) ∧ ((True ∨ (True ∨ p2)) → False)) ∧ p1) ∨ ((False → (p1 ∧ p2)) ∧ (True ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249730694327173546237667530019 : ((p5 ∨ p5) ∨ (((((((p3 ∧ ((True ∨ p4) ∨ (True → p5))) → p1) ∨ False) ∧ p4) → p3) ∧ ((False → p3) ∨ True)) ∨ ((p4 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303744963553476704485648032213 : (p1 ∨ (((((p1 ∨ (((p5 ∧ ((p3 ∨ False) → (p2 ∧ p2))) ∨ p2) ∧ (p5 → (p4 ∧ p3)))) ∨ ((p3 ∨ p1) → True)) ∧ p5) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136141406081268311611225550940 : ((((p5 → (((p1 → p4) ∨ p2) ∧ False)) → p5) → (p4 → ((p1 ∨ (p1 ∧ (True ∨ (p4 → p1)))) ∨ (p4 ∨ p5)))) ∨ ((False → p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635343654306050075168710512942 : (((((((p5 → (p1 ∧ (((False ∨ (False ∨ (p4 → p5))) ∨ p3) → True))) ∧ p5) → (p3 ∧ p3)) ∧ (((p4 ∨ p5) ∨ True) ∧ p1)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721149101136033985479460388902 : (((((p2 → p1) ∨ (False ∨ False)) → ((p5 → (p5 → ((False ∨ (p1 → ((False ∨ p3) → p5))) → p1))) ∨ ((True ∨ p5) ∨ (p1 ∨ p5)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184680790554124277156736629913 : (((p4 ∨ ((p5 ∨ (p2 ∨ p4)) ∧ p1)) ∨ ((True → True) ∨ p3)) ∨ (p1 ∨ ((True ∨ (p5 ∧ p1)) ∧ (((p4 ∨ p5) → p2) → (p4 ∧ p2))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260088728639835987079661329541 : ((p2 → False) → (p1 → (((p3 ∨ (p3 → (p1 → ((p4 ∧ (p2 ∨ (False ∨ (p4 ∨ (p4 ∧ p2))))) → ((p2 ∨ p2) ∨ p5))))) ∨ True) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49142272880483590850164173002 : ((((p4 ∧ (p2 → ((True ∨ (p1 ∨ (p3 → p1))) → True))) ∨ (p4 ∨ (p5 → (p5 → ((p3 ∨ p4) ∧ False))))) ∨ ((p2 ∧ p5) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616294116839258733622774076658 : (((((((p1 → True) ∨ (p1 ∨ ((False ∧ p5) → False))) → (p3 ∧ p5)) ∨ ((p2 ∧ False) → ((False → False) → ((p4 ∨ False) ∧ p4)))) ∨ p1) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47609949546145198805606611330 : (((p4 → ((((p4 → ((p1 → p4) ∨ p1)) ∧ p1) ∧ False) ∨ (((p5 ∧ p2) ∨ ((p3 → (p2 ∧ p3)) ∨ True)) ∨ p5))) ∨ (p1 ∧ p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307689415528302613585553567829 : (p1 ∨ (p2 → ((True ∧ (((p4 ∨ ((p4 ∧ (p4 ∧ p3)) ∧ p3)) → True) ∧ True)) → ((True ∨ p1) ∧ (((p1 → p4) → p5) ∨ (p3 ∨ True)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322584504158855679289581978288 : (p5 ∨ ((True → (((p3 ∨ (False ∧ (((p2 ∨ p4) ∧ True) ∧ ((p4 → p1) ∨ (True → False))))) ∨ p5) → ((p4 ∨ p5) ∧ (p1 ∨ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



