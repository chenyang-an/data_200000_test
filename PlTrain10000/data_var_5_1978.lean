variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314161965723431881966639758636 : (p3 ∨ (((((p4 ∨ p3) → ((((p5 ∧ (p1 → p4)) ∨ p1) ∨ ((False → False) → (p5 ∧ p2))) ∨ p4)) ∨ True) ∨ p1) ∧ (p4 ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123838819847356040583810296714 : (((((False ∨ (p2 → ((p3 ∨ ((p2 → True) ∨ True)) ∨ p3))) ∨ False) ∨ True) → ((p2 ∨ True) ∧ ((True ∧ False) ∨ (True ∧ False)))) → (p2 ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∨ (p2 → ((p3 ∨ ((p2 → True) ∨ True)) ∨ p3))) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((False ∨ (p2 → ((p3 ∨ ((p2 → True) ∨ True)) ∨ p3))) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49715208042126976060262946374 : (((True ∧ ((p2 ∨ True) → ((True ∧ (p2 ∨ (False ∨ ((p2 ∧ (p4 ∨ p5)) ∨ (p4 ∨ (p5 ∨ False)))))) → p5))) → (True → (p4 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172407059272811774533142381973 : (((((p5 ∨ p5) ∧ p4) ∧ p5) ∧ (p5 ∧ (p5 ∧ (((p1 → True) → p1) ∨ p4)))) ∨ ((True ∨ p5) → ((False → True) ∨ (False ∧ (p4 ∧ p2))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198456185805664221992535874754 : ((p5 ∧ (((p4 → p2) ∧ p5) → (p3 ∨ p1))) ∨ ((p4 → (p3 → (((p3 ∨ ((False ∧ p3) → (False → p2))) ∧ (p4 → p5)) ∨ p3))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314209820413737100374030225461 : (p3 ∨ ((False ∨ (((True ∧ p4) ∧ p4) ∨ (((p3 ∧ (p2 ∧ p5)) ∨ (p3 → p1)) ∨ ((p5 ∧ True) → (p2 → p2))))) ∧ ((False → False) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342182608222743664272133369449 : (p2 → ((p2 → ((((p5 ∧ False) ∧ True) ∨ (True → (p2 ∧ True))) → (False ∨ ((p1 ∧ p5) → (p3 ∧ p1))))) ∨ (True ∨ ((p5 ∧ p5) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658791280988385121631198788602 : ((((p5 ∨ (p3 ∧ (p4 ∧ (((p1 → p1) ∧ (((p2 → False) → ((p2 → ((p1 ∧ p5) ∨ p3)) ∧ p3)) ∨ p2)) → p3)))) ∨ (p4 → p4)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_42067903570410039814313817086 : ((((p5 ∨ p5) ∨ (p4 ∨ (((p1 ∧ ((False ∨ p2) → p1)) ∨ ((p2 → p2) ∨ (((True ∧ (p4 ∨ p4)) → False) ∨ p2))) ∧ p2))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221235579560572494090015931065 : (((p2 ∨ True) ∨ p4) ∧ (((p1 → True) ∧ (True → ((((((True ∨ True) → p3) ∧ p4) ∧ p1) ∧ (p5 ∨ p2)) ∧ (p4 ∨ p3)))) → (p1 ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2174414481748991632570723149 : (((((((p5 ∨ p5) ∨ p5) ∧ False) ∨ ((False ∧ False) ∨ (True ∧ False))) ∧ p2) ∧ p5) ∨ ((p2 → False) → (((p5 → p2) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134615206698566128962545550891 : (((((p2 ∨ (p5 → (p1 → p3))) → (((p2 ∧ (p2 ∨ (p4 ∨ True))) ∧ p2) ∨ p3)) ∨ (p4 ∨ (False → p2))) → p2) ∨ ((True ∨ p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40619796295070848222601148714 : (((((False ∨ (((True ∨ (p3 ∧ (((False ∨ (p1 ∨ p2)) → (True ∧ (p5 ∨ p4))) → p4))) → False) → (p4 ∧ p1))) ∨ p5) → p1) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615540343293076496291649744504 : (((((((True ∨ p4) ∧ (p5 ∨ p1)) ∨ (((p3 ∨ (p5 → p1)) ∨ p4) → (p1 ∨ p2))) → (p3 → ((True → p1) → (p1 → False)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_231253863941651265739430136030 : (((p4 ∨ p3) ∨ p1) → ((p5 → True) → ((p5 → p3) ∨ (p2 ∨ (((((p2 → p2) ∨ ((p3 ∧ p4) → True)) ∧ (p3 ∧ False)) → p5) ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h7.left
        let h13 := h7.right
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h19.left
      let h25 := h19.right
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115395544879041684111305446350 : (((p1 ∧ ((p2 → ((p5 ∨ p5) ∨ p5)) → False)) ∧ ((False → p4) ∧ ((p2 ∧ ((p3 ∧ True) → ((p1 ∧ p5) ∨ False))) ∨ p1))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68233813785138998364427893757 : ((p3 → ((((True ∧ (p5 → p4)) → p5) → (p2 ∧ (((True ∨ ((p3 → p5) → ((True ∨ p2) ∧ True))) ∨ False) ∨ (False ∨ True)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115303845141136247585439114552 : ((((p3 ∧ (p5 → (p2 → ((p2 ∧ p3) → p3)))) → p2) → (p3 → ((p4 ∨ (True ∧ ((True → p3) → (p2 ∨ p4)))) ∧ p2))) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (p3 ∧ (p5 → (p2 → ((p2 ∧ p3) → p3)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∧ (p5 → (p2 → ((p2 ∧ p3) → p3)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h11
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180112178105919360794009326250 : (((((p3 ∧ (p3 ∨ (p5 ∨ p4))) ∧ ((p1 → False) → p3)) ∨ True) → p1) → ((((False ∨ p5) → (p2 ∨ p1)) ∨ ((True → p2) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138829455839363561391231268487 : (((p3 ∧ (((((((p5 → p5) ∧ p3) → p2) ∧ False) ∨ p3) → p1) ∨ (((p1 → (p5 ∨ p5)) ∧ p1) ∧ p3))) ∧ p3) → (p4 ∨ (p1 ∧ p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (((((p5 → p5) ∧ p3) → p2) ∧ False) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : (((((p5 → p5) ∧ p3) → p2) ∧ False) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h15
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323488051548183426000756859243 : (p5 ∨ (((((p1 → ((((p1 ∨ False) ∨ (p4 → p1)) ∨ p2) → p5)) ∧ (p3 → p5)) → (p1 → p5)) ∨ (p1 → p2)) ∨ ((p3 ∨ p4) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((p1 ∨ False) ∨ (p4 → p1)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_842481096539591264938101244010 : (((((((p4 ∧ ((p4 ∧ ((p5 → (p3 → p5)) ∧ p4)) ∨ p5)) ∨ p1) ∨ True) → ((p2 ∧ True) ∨ (False ∧ (True ∧ (p2 ∨ p5))))) ∨ p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p4 ∧ ((p4 ∧ ((p5 → (p3 → p5)) ∧ p4)) ∨ p5)) ∨ p1) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172302316928387046595927877169 : ((((((p4 → p3) ∧ p3) ∨ False) → (p1 → p4)) → ((False → p5) → (p4 → p5))) ∨ (True ∧ ((p3 ∨ (p1 → True)) ∨ (p4 ∨ (p4 → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114916416281119753256038444880 : ((((False → (((((False ∧ p5) ∨ (p3 ∨ False)) ∧ False) ∧ p2) ∨ p1)) ∨ p1) → ((((p4 → p5) ∧ False) → True) ∧ (p1 → p3))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183947788712640837143664976291 : (((p3 ∨ ((p3 ∨ (False ∨ True)) → (p5 ∨ (p4 → True)))) ∧ p2) ∨ (((((p4 ∨ ((p5 ∨ p1) ∨ p1)) → True) ∨ p2) → (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191298752299480731471677901044 : (((p1 → p2) ∧ (p2 ∨ (((False ∨ False) ∧ p2) ∨ p5))) ∨ (p2 ∨ (((True ∧ (p3 → p5)) ∨ (((p1 ∧ p5) ∨ True) ∨ True)) ∨ (p3 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_147988944605278131034758221078 : ((((((p2 → (p4 ∨ (p2 ∧ p3))) → p3) ∨ ((p3 ∧ (True ∨ (True ∨ p1))) ∨ p4)) ∨ p4) ∨ (p2 ∨ False)) ∨ (False → ((p3 ∧ p3) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231947663778653903347709532772 : (((p1 ∨ False) → p4) → ((True → (False ∧ (((False ∧ p4) → p1) → ((p4 → ((p1 → p1) ∧ (p3 ∧ p5))) → p4)))) → ((p4 ∨ p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345712788619444263274854475884 : (p3 → ((p1 → (p1 ∧ (((((True ∧ p3) ∨ p3) → False) ∨ ((p5 ∨ ((p2 → ((p4 ∧ p5) ∨ (True → p1))) ∧ p1)) → p4)) ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185497049286436668643746692146 : ((p2 ∨ ((p1 ∨ (p5 ∨ (p5 ∨ (p4 → p2)))) ∨ (True ∨ p3))) ∨ ((False ∨ ((p1 → p3) → ((p3 → ((False → False) ∧ p2)) ∨ p5))) ∧ p1)) := by
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
theorem thm_5_vars_166450695822452655434565217797 : ((p2 ∨ ((((p4 → p5) → (p1 ∧ ((p4 ∧ p4) ∧ True))) ∧ p3) ∧ ((p5 ∧ False) → False))) ∨ (False → ((p2 → True) ∨ ((p4 ∨ True) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115750184669813796260987323599 : (((True ∧ (p2 ∨ (p2 → (p3 ∨ True)))) → ((p4 ∧ (((False → False) ∧ p5) → (True ∨ ((p1 ∨ p5) ∨ p5)))) ∨ (p2 ∧ False))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234731658763624497089036905336 : ((p4 → (p5 ∨ p5)) → ((p2 → ((p4 ∨ (p2 → p4)) → ((((p3 → ((((p3 ∨ p2) → p4) ∧ p3) → p5)) ∨ p5) ∨ p1) ∧ p4))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299266542686755676701121536412 : (False ∨ ((((p1 ∧ p4) ∧ ((False ∨ True) ∨ ((p4 ∨ p2) ∧ (((p5 → False) ∨ p5) → p2)))) ∧ ((p2 → ((p2 ∧ p2) ∧ p4)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_379814686664809771603365493258 : (((((((p3 ∨ (p4 ∨ (((((p1 → p4) ∧ ((p2 → p1) ∨ p3)) ∨ (p2 → p1)) ∧ (p2 ∨ p3)) → True))) → False) ∨ p1) ∧ False) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_136338658073203468344728071735 : (((p3 ∧ ((p4 ∧ False) ∨ p5)) ∧ (False → (True → ((p1 ∧ False) ∧ (((p2 → (False → p3)) → p3) ∨ (p1 ∧ p2)))))) ∨ (p3 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727589703370546834470782531402 : ((((p5 ∧ (p5 ∧ True)) ∨ (((True → p1) ∨ p4) → (((((p3 → ((p3 → p5) ∨ p1)) ∧ ((True ∧ p1) ∨ p3)) → False) ∧ p4) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336346363206200856743294907987 : (p1 → (((p5 ∨ False) ∧ (((((True ∨ True) ∨ (((p4 → (True ∨ False)) ∨ (p2 → (True ∨ p5))) ∧ (p5 → False))) ∧ p2) ∨ p1) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166012350875747951741517539150 : (((p2 ∨ False) ∨ (((p2 ∧ (p1 ∧ p4)) ∧ (p4 ∧ (((p5 ∧ p4) → p3) ∨ p5))) ∨ p4)) ∨ ((((p1 ∨ False) ∧ p3) ∨ p2) → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134081840194084879345268558966 : ((((((((True ∧ True) → p1) ∨ p1) → (p1 ∧ p1)) ∨ (((True ∧ p3) ∨ p4) → (p4 ∧ (p5 ∧ p2)))) → p5) ∨ p2) ∨ (False ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304389748248643886335860201950 : (p1 ∨ (((True → (p1 ∧ p2)) ∧ (((((p5 ∧ (p2 ∨ p2)) ∧ p1) ∨ p4) ∨ (((p1 ∧ p4) → p1) ∧ p1)) → (p3 → (p3 → False)))) → p2)) := by
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
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119396277032592628837144392757 : ((p4 → ((p1 ∨ ((p5 ∨ True) ∧ ((p4 → (p1 ∧ ((False → p4) → (p1 ∨ ((p1 ∧ p2) ∨ (p1 → p4)))))) ∨ p3))) ∧ True)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318584722782191548904577590192 : (p4 ∨ ((((((p1 → ((p4 ∨ p2) → p1)) → p2) ∨ ((p4 ∧ True) ∨ p1)) ∨ ((p5 ∨ p1) ∨ p3)) ∧ ((p4 ∨ p4) ∨ p2)) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62322567953988464221440382013 : ((p3 ∧ (((p1 → (p5 → (((p5 ∨ (p5 ∨ (p4 ∨ p4))) ∨ p3) → (((p2 ∨ (p1 → True)) ∨ p2) ∧ p1)))) ∨ p2) → (False ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430786731478953053627094386554 : (((((p5 ∧ p1) ∧ (((((p1 → (p1 ∨ True)) ∨ ((p5 ∨ (p3 ∨ p4)) ∧ (p2 ∧ False))) ∧ (p5 ∧ p3)) ∧ p4) → p1)) ∨ (True ∨ p4)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_148263532142236986370548661218 : (((p3 ∨ (p4 ∧ ((p5 ∨ p5) → (p3 ∨ ((p4 ∧ (False ∨ p1)) → (p3 → p4)))))) ∨ (p5 ∧ (True ∨ True))) ∨ (((True → p5) ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157834464904844427711581150493 : (((True → (p2 ∨ (((p4 → p5) ∨ (p1 → (True ∧ p1))) ∨ p4))) → (p2 ∧ (p1 → (p4 → p3)))) ∨ (p5 → (((p4 → False) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_304718750106820326548682027805 : (p1 ∨ ((((p3 ∨ ((False ∧ (p3 ∨ ((p1 ∧ ((False ∧ True) ∨ (p2 → p3))) ∧ True))) ∧ False)) ∨ p1) → ((False ∨ False) ∨ True)) ∨ (p4 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135743448846322095890833371649 : (((((p4 ∨ False) ∨ ((p4 ∨ False) ∨ False)) ∨ (p5 ∧ ((p3 → True) ∧ False))) ∨ ((p4 → p4) ∨ ((p3 ∨ p5) → p4))) ∨ ((p1 ∨ p2) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57398995614751847242013641793 : (((False ∨ (p1 ∨ p2)) ∨ (((((p3 ∧ True) ∨ (p1 → (p5 → p5))) ∧ p3) ∧ (p2 → (p5 → (False ∧ (p4 ∨ True))))) → (p5 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206250431349368298441273532324 : ((False ∨ (((False → False) → p3) ∨ p4)) ∨ ((p3 ∨ False) ∨ ((False ∧ p4) ∨ ((True → ((p5 ∧ p1) ∧ (p5 → (True ∨ (False ∨ p3))))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356805156050094640666968901446 : (p5 → (((True → (False ∧ p3)) → True) ∧ (((p1 ∨ ((((False ∨ (p1 ∨ p2)) ∧ (p3 ∧ False)) ∨ p3) ∧ p2)) ∨ (p1 ∨ (True ∨ p2))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_78536240553077631940376002181 : (((((p2 ∧ (p4 → p3)) ∨ ((p3 ∨ (p3 → False)) ∨ (((p4 ∧ p1) ∨ (False ∨ (p4 → (p2 → p2)))) ∨ p1))) → False) ∧ (p2 ∨ p3)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p2 ∧ (p4 → p3)) ∨ ((p3 ∨ (p3 → False)) ∨ (((p4 ∧ p1) ∨ (False ∨ (p4 → (p2 → p2)))) ∨ p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p2 ∧ (p4 → p3)) ∨ ((p3 ∨ (p3 → False)) ∨ (((p4 ∧ p1) ∨ (False ∨ (p4 → (p2 → p2)))) ∨ p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114370690812930168062490803836 : (((((p2 → p4) ∧ (((p2 ∧ p2) ∧ (p4 → p1)) ∨ (((p1 ∨ False) → True) → p1))) ∨ True) ∨ (((p4 ∧ p4) ∨ p4) ∧ p5)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113672323073853293190347155321 : ((((((p3 → (p4 ∨ p1)) ∨ p2) ∧ (((p1 → ((p3 ∨ p4) → (p4 ∧ False))) ∧ p4) → (p2 ∧ p5))) ∨ p1) → (True ∧ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51562066580471577413252160184 : (((False ∨ (((False → p4) → (((p2 ∨ ((p3 → True) → p1)) ∧ p4) ∧ p1)) ∨ (p2 → False))) → (p4 ∨ (p1 ∧ ((p2 ∨ True) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321946455990050336122373426745 : (p5 ∨ (((((((False ∧ p4) → False) → (True → ((p4 ∧ (False ∧ (p4 ∧ p5))) → True))) ∨ p2) → p5) ∨ ((p2 ∧ False) → (True → p5))) ∧ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647485383487957267157689852886 : ((((p4 → (p1 → (p2 → (((p5 ∨ (p2 ∧ p4)) ∨ p3) → (((False ∧ p2) ∨ (p2 ∧ False)) ∧ (p2 ∧ ((p5 → p5) ∨ False))))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119580571136415483967587837437 : ((p5 → ((p2 → (p4 → True)) → (((p1 ∨ (p4 → (False ∧ ((False → p1) ∧ ((False ∨ p4) → (p4 ∨ p1)))))) ∧ p5) → p1))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112588527411719810996344118477 : (((((((p2 → (p5 → ((p1 ∨ ((p3 ∧ p2) ∨ False)) ∨ False))) ∧ p4) ∧ p1) ∧ ((p5 ∧ p1) ∧ p3)) ∧ (True → p3)) → False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653703401926226580895064719075 : ((((((p3 ∧ (False ∨ (p2 → (True ∧ (p1 ∧ (p4 ∨ ((True ∧ (True ∨ ((p5 → p3) ∧ p3))) ∧ p4))))))) → p2) ∧ p1) ∨ (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260585322083717376061125573239 : ((p3 → p2) → ((((((p1 ∧ ((True → (p1 ∨ p4)) ∧ p5)) ∨ p2) ∧ (((p3 → (p1 ∨ False)) ∨ True) ∧ p1)) ∧ (p2 ∨ p1)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166430376085946485906353907017 : ((p1 ∨ (p2 ∧ ((p1 → p2) → (((p1 ∨ (p4 ∧ p4)) ∨ ((p3 ∧ p1) ∨ p2)) ∨ p5)))) ∨ (False → ((p5 → True) → ((False → p3) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51742284291525279219433440794 : ((((p3 ∧ (p1 ∧ p5)) ∨ ((((((p4 → p2) → True) → p5) ∧ p4) ∨ False) ∨ True)) ∧ ((p2 → p5) ∨ ((True ∧ False) → (p3 → p4)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_135945030545367305790211128692 : ((((p1 ∨ (((False ∧ p1) ∧ False) ∨ p3)) ∧ (p5 ∨ False)) ∧ (((((p1 ∧ False) ∨ p2) → p5) ∧ (p3 → p5)) ∧ p2)) ∨ (False → (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114082743063426726594368960778 : ((((True ∨ (p2 ∨ p2)) → ((((p5 ∧ p1) ∨ (((p3 ∨ (p1 → p2)) ∧ True) ∨ True)) ∧ p3) ∨ p3)) ∨ ((True ∨ p1) ∨ p2)) ∨ (p3 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311777216278376536540136779893 : (p2 ∨ (False ∨ ((p3 ∨ False) ∨ ((False → True) ∧ (((p3 ∨ (False → ((p2 → p1) ∧ (p4 ∧ p1)))) ∨ (True ∧ p4)) ∨ (p4 → (True → p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64304659312194496588698792718 : ((False ∨ (p5 → (p2 ∧ ((p1 ∧ True) ∨ ((p2 ∨ p3) ∨ (((((p5 ∧ (False ∨ p4)) ∨ ((False ∧ p2) ∨ p1)) → p3) → p1) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45887145260638429155422082425 : (((p3 → (True ∨ (((p5 ∨ (p2 → p3)) → (p1 → ((True ∨ p2) ∧ (((p5 → p5) ∨ False) ∧ ((p3 ∧ p4) → p1))))) ∧ p4))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248462352961541177177907482378 : ((p2 ∨ p5) ∨ (((True ∨ p3) → (p3 → ((False ∧ False) ∨ ((p4 ∨ True) → True)))) ∨ ((((p5 ∨ p4) ∧ p1) ∧ (True ∨ (True ∨ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152119950451878457686466091350 : ((((((p3 ∨ p1) ∧ p2) ∧ p5) ∨ (p1 ∨ p3)) ∧ ((((p1 ∨ False) → p3) → (p4 → p5)) ∧ (p1 ∨ p2))) → (p5 ∨ ((p5 ∨ p1) ∨ p2))) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h3.left
      let h22 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h3.left
      let h27 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65394510463478019938876042091 : ((p3 ∨ (((((p3 ∧ p4) → False) ∧ p5) ∧ True) → (True ∧ (p3 → (((p3 → True) → ((p4 ∧ p3) → (False ∧ False))) ∨ (p4 ∧ True)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h11 : (p3 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h8.left
  let h14 := h8.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h15 : (p3 ∧ p4) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h14
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h16 := h5 h15
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325081045442201884862128936259 : (p5 ∨ ((True → False) → (p4 ∧ (((((p1 ∨ p5) → (False ∨ False)) ∧ True) ∨ p2) ∧ (True → (((False ∧ (p2 → False)) ∨ (True → p1)) ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37185279001132377901327430749 : ((((((((((p1 ∨ p5) ∧ True) ∧ False) → p5) → True) → p5) → ((((p1 → p3) ∨ True) ∨ ((p5 ∧ True) → p2)) → p4)) ∧ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46837520982264036977096427115 : (((((p5 ∧ (((p3 ∨ p5) → (p1 ∨ p4)) ∧ (False ∨ p2))) ∨ ((p4 ∧ (p3 ∨ (p3 ∨ True))) → (p5 ∧ False))) ∧ p1) ∨ (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172749045022559417207234884563 : (((p1 ∧ p2) → ((True ∨ p3) → ((p4 ∨ (False ∧ p3)) ∧ (False ∧ (p1 ∨ False))))) ∨ (True → (((True → p2) → p5) → (True ∧ (p2 → p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True → p2) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218031431409440917205613822318 : (((p1 ∨ p1) ∧ (True → True)) → (((p3 ∨ (((True ∧ (((False → (True ∨ p1)) → p1) ∨ p1)) ∧ p2) ∧ p4)) ∧ True) ∨ (False → (p2 ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593269931284328065104106760319 : (((((p5 ∨ ((p4 ∧ (p4 ∧ ((False → ((p2 ∧ False) → (p3 ∨ (True ∧ p1)))) → p2))) ∨ (p3 ∨ p2))) ∨ (p3 → (p3 ∨ p5))) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156663385372296789311169227584 : ((((p2 ∨ ((p1 → (((p2 → False) ∧ (p5 ∨ ((p3 ∨ False) ∨ p4))) ∨ p5)) ∨ p5)) → p3) ∧ p5) ∨ (p5 ∨ (False → (p2 ∧ (p1 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328091890099108980429719157770 : (True → (((((p4 ∧ p2) ∨ (p5 ∨ (False → (((p2 → p3) → p3) → (p5 → (p1 ∨ p5)))))) ∧ (p2 → False)) ∧ False) ∨ ((False ∧ p3) → p4))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700628347622275421204158726381 : ((((p2 → ((True → p5) ∧ (((False ∨ p4) ∨ (p2 → p1)) ∨ p2))) → (p5 ∨ ((True ∧ ((p5 ∨ p4) → ((True ∧ True) → p5))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118805424398450074851918668750 : ((True → ((p5 ∧ (p3 ∧ (p5 → (p5 ∧ (True ∧ ((p5 → (p4 ∧ (p3 → (p3 ∧ (p4 → (p2 ∨ p4)))))) ∨ p5)))))) ∧ p3)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185271768778675751459230680233 : ((p1 ∧ (p4 ∨ (True ∧ ((p1 → (p4 ∨ (p3 ∧ True))) ∨ p1)))) ∨ (p1 → (False ∨ ((p4 ∧ p1) ∨ ((p1 → ((p1 ∨ False) → p5)) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745319634342790672766394146899 : ((((p5 ∧ p2) → ((((False ∧ (((p3 → (p5 → (p3 ∨ p5))) → (p3 ∨ p1)) ∨ ((p4 → p5) → True))) ∨ p5) ∨ p1) ∧ (p5 → p5))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246754998592354737459936862710 : ((p5 ∧ p5) ∨ (((True ∧ ((p1 ∧ True) → (p2 ∧ (p3 ∨ ((True ∨ p1) ∨ True))))) ∨ (p4 → (p2 → (p2 ∧ p1)))) ∨ (True ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317878585232579283604246312842 : (p4 ∨ (((p2 → p3) → (p4 ∧ ((((False ∨ p1) ∨ ((p2 ∨ (p1 ∨ True)) ∨ (True → p1))) ∨ ((p1 ∨ (p5 → p1)) ∧ p3)) ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674554397749510379669611130409 : ((((True → (((p2 ∨ ((p4 → (False ∧ ((p5 ∨ False) ∨ (False ∨ ((p2 ∧ p3) → p3))))) ∨ p1)) ∧ p4) ∨ p5)) → (p4 ∧ (p3 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259035300779963178417729267934 : ((True → p4) → ((p1 → (p3 ∧ (False ∧ p3))) ∨ (((p2 ∨ ((p4 ∨ ((p1 ∧ p4) ∨ p3)) ∨ p1)) ∨ (False ∧ ((p4 ∧ p5) → True))) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39570754535268146325882270650 : (((p1 ∨ ((False → (p2 → ((True ∧ True) ∧ p4))) ∧ (p3 ∨ ((p3 ∧ ((p5 ∨ p4) ∨ ((False → p3) ∧ (p2 → p1)))) ∧ p5)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677156268380890942794968003046 : (((((((p4 ∨ (True ∧ (p5 → True))) → (p2 ∧ (p3 ∨ ((p5 ∨ False) ∧ (p5 ∧ True))))) ∧ p5) ∧ p5) ∨ (False ∨ (False ∧ (p4 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700443436897824593631872115699 : ((((False ∨ (True ∨ ((p1 → p3) ∧ (p2 ∧ (p1 ∧ (p2 → p3)))))) → (((p3 → (p2 ∧ (p3 ∨ p5))) → p4) → ((False ∧ p4) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305660610991027004017923521810 : (p1 ∨ ((p4 ∨ (((p3 ∨ True) → p2) → ((p4 ∧ True) ∨ True))) ∧ (p3 → (((((p5 ∨ (p1 ∨ p3)) ∧ p3) ∨ p4) ∧ (True ∧ True)) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350096953882237882343125413916 : (p4 → (((p4 ∧ (p5 ∧ ((p2 → ((p1 ∨ ((p4 → False) ∨ ((False ∨ p3) → False))) ∨ True)) ∧ (True → p3)))) ∨ (p2 → (p4 → p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16937229907071278560591613421 : (((False ∨ (((((False ∧ (p1 → p4)) → ((p4 → p1) ∨ p3)) ∨ (p1 ∨ (p2 → p2))) ∧ (False ∧ p1)) ∨ p5)) ∨ (p1 ∨ (False ∨ True))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_90713733241771822071267072978 : (((False ∨ p5) ∧ ((True ∨ (p3 ∧ p3)) → ((((True ∧ p2) → (((False ∧ False) ∧ p5) ∨ p4)) ∧ (((p3 ∧ p1) ∧ p3) ∧ p5)) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (p3 ∧ p3)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177635336786091751431102214082 : ((((((p1 → p4) → p2) ∧ ((p1 ∨ p5) ∧ (True → False))) ∧ True) ∧ p4) ∨ ((p2 ∧ (False → (False ∧ p4))) ∨ ((p4 ∨ (False → p5)) ∨ False))) := by
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
theorem thm_5_vars_135971699903742927191060382222 : (((((False → (((p4 ∧ False) → False) → p3)) → p5) ∧ p1) ∨ (True ∧ ((((p5 ∨ p3) → False) → p1) ∨ (p4 ∨ True)))) ∨ (p5 → (False ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190841844294527842839777368530 : (((((p1 ∧ (p1 → p3)) → p1) ∧ p3) → (False ∨ p4)) ∨ (((p5 ∨ (((False → False) ∧ p5) ∧ p1)) ∧ (p2 ∧ p3)) → (p3 ∧ (True ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h15.left
    let h25 := h15.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231468872287992977283036134225 : (((p3 → True) ∨ p3) → ((((p5 ∧ ((((p1 ∧ p4) → p1) → True) → (((p3 ∨ p4) ∧ True) ∨ p5))) ∧ p4) ∧ p3) ∨ ((False ∧ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765769037867251102542194332513 : (((p4 ∧ ((p2 ∧ (((p3 → p1) ∨ (p4 → True)) ∨ True)) ∧ (((True → (p4 ∨ (((True ∧ (p4 → p2)) ∧ p4) → False))) → False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



