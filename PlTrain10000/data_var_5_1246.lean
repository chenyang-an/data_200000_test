variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53129136002492095719501557302 : ((((((p2 → (p5 ∨ ((p5 ∧ p5) ∨ False))) ∨ True) → False) ∧ p5) ∨ (False ∨ ((p4 ∨ ((p2 ∨ ((True → p5) ∨ p1)) ∨ p1)) ∨ True))) ∨ p2) := by
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
theorem thm_5_vars_171927423395670844255773675320 : ((((p5 ∧ ((True ∨ p2) → (p5 ∨ (p1 → (p5 ∨ p4))))) ∧ p1) ∧ (p2 ∧ p5)) ∨ (((p2 ∨ (p3 ∧ (p3 ∧ True))) → False) → (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ (p3 ∧ (p3 ∧ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658231580794550854669398267860 : ((((p5 ∧ (((((False ∨ p2) → p1) → p5) ∧ False) ∧ ((p5 ∨ (((False ∨ False) ∨ (p3 ∨ (p4 ∨ False))) ∨ p2)) → p5))) ∨ (False → True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_225491149399245996575701683672 : (((p5 ∨ False) ∧ p2) ∨ (p1 → ((p5 ∨ (False ∨ p5)) → ((p1 → False) → ((True ∨ ((False ∧ False) ∨ (((p1 ∨ False) → p5) ∨ False))) ∧ p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241489635529409948228872844324 : ((False → p2) ∧ ((p2 ∧ p4) ∨ ((p5 ∨ ((False ∧ ((p1 → ((p3 ∨ p2) → (p5 ∨ False))) ∨ ((p4 ∧ p4) ∧ False))) ∨ (False ∨ p4))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136096439081526719728578584519 : ((((True → ((p4 ∧ p2) → (p2 ∧ p1))) ∨ p4) ∨ (((((p1 → (p2 ∨ p5)) → p2) ∧ p4) → p1) ∨ (p1 ∨ p2))) ∨ ((p2 ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46298706675296283495764683687 : ((((((((((p2 ∧ p5) ∧ p3) ∨ p4) ∨ p2) → p3) ∧ ((p1 ∨ p2) ∨ p2)) ∧ (p2 ∧ p1)) → ((p3 ∧ True) ∧ p1)) ∧ (p2 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : ((((p2 ∧ p5) ∧ p3) ∨ p4) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h15 : ((((p2 ∧ p5) ∧ p3) ∨ p4) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h16 := h4 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h3.left
    let h19 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h20 : ((((p2 ∧ p5) ∧ p3) ∨ p4) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h21 := h4 h20
    -- One of the premise coincides with the conclusion.
    exact h21
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h23.left
      let h29 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h23.left
      let h32 := h23.right
      -- One of the premise coincides with the conclusion.
      exact h32
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h23.left
    let h35 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h35
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149794504443833074181864140400 : ((False ∨ ((p1 ∨ (p2 ∨ p4)) → ((p4 → p5) ∨ ((p3 ∨ p3) ∨ (((p1 → p2) ∧ p1) → (p4 → p2)))))) ∨ ((p1 → p5) → (True → p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
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
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h16.left
      let h19 := h16.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58577561894820449786107446735 : (((True → p3) ∧ ((False ∨ False) ∨ (True → (((p3 ∨ (p5 ∨ p2)) → ((False ∧ ((p5 ∧ False) → (p5 → p4))) ∨ False)) ∨ (p1 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704618713460456527352179788928 : (((((p3 ∨ p1) → (p2 ∧ ((True → (True → False)) ∧ p3))) → (p4 ∨ (((p4 ∨ p3) ∧ True) → (((p2 ∨ (p1 → p5)) ∨ p1) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_993770839163959573909015415305 : (((p5 ∧ ((((p2 → (((p3 ∨ (p1 → p5)) ∧ False) ∧ ((p3 ∨ p4) ∨ p3))) → (p4 ∧ ((p3 ∧ p2) → (p3 → p3)))) → False) ∧ p2)) → p3) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → (((p3 ∨ (p1 → p5)) ∧ False) ∧ ((p3 ∨ p4) ∨ p3))) → (p4 ∧ ((p3 ∧ p2) → (p3 → p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h16 := h4 h6
  -- False on the left can always be used.
  apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304092641029405688654233879470 : (p1 ∨ ((True → ((p1 ∧ (True ∧ ((p1 ∨ ((p4 ∨ True) → (True ∨ False))) ∨ True))) → (((p3 ∨ False) → ((p2 ∧ p5) ∨ p1)) ∨ p4))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148431158062592734048476040466 : ((((p5 ∧ p1) → (((False ∨ ((p5 ∧ (p5 → False)) ∧ p1)) ∧ p5) ∨ True)) → ((p4 ∨ (p1 → p1)) → p1)) ∨ (((p5 ∧ p3) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629085088700880622746457646621 : (((((((True ∨ ((p5 ∧ p1) → (True → (((p1 ∨ p5) ∧ ((p4 → (p3 → False)) ∨ (p2 ∧ p2))) ∨ True)))) ∨ p3) ∨ p3) ∨ p3) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177997331547029716553537226483 : (((False ∨ (p2 ∧ ((True → (((True ∧ p4) → p4) → p1)) → p1))) ∨ p3) ∨ ((p2 ∨ ((p3 → (p2 ∧ (False → (p4 ∨ p3)))) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_583645517014428231926744777414 : (((p5 → ((((p1 → ((((False ∧ p5) → p5) ∧ p2) ∧ p1)) ∨ (p5 ∨ (p4 ∧ p5))) ∨ p4) → (p5 ∧ (((p1 ∧ p4) ∧ True) ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60731499709059883057278170435 : ((True ∧ ((((p5 → p3) ∧ p2) ∨ p3) → (((p2 ∨ (True ∨ (p1 ∨ ((False → p2) → (((p5 → p1) → p5) ∧ True))))) ∨ p1) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141142304747958227859619914472 : ((((True ∨ ((p1 ∨ p2) ∧ False)) → p3) ∧ ((p5 ∧ p4) ∧ (((((p2 ∨ (p4 ∧ p3)) → p1) ∧ True) ∨ p5) → p4))) → ((p5 → p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ ((p1 ∨ p2) ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h8
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217279644473589301788689333346 : (((p3 ∧ (p2 ∧ p2)) ∨ p5) → ((((p3 ∨ (True ∨ ((p1 ∨ (p1 ∨ (p4 → (p3 → p3)))) ∨ p1))) ∨ (p5 ∧ p2)) → (p2 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134661205207093119535613179035 : (((((p5 ∧ (p2 ∧ p4)) ∨ (True → (p4 ∨ (p4 ∨ p1)))) ∨ ((p5 ∧ (True → ((p2 ∨ p4) ∧ p2))) ∧ p2)) → False) ∨ ((p2 → p2) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350127981638255117030506884930 : (p4 → (((True ∨ (p3 → (((((p3 → p3) ∧ p3) ∧ True) ∧ p3) → (p1 ∧ (True → True))))) → ((p5 ∧ p2) ∧ ((True ∧ True) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111919652658599644946622737714 : ((((((p4 ∧ ((p4 ∨ False) → (True ∨ p2))) → (False → p1)) ∧ p1) → (False ∨ (True → ((p5 → (p2 ∧ p5)) → p1)))) ∨ p2) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181032061950985624885757402555 : (((p2 → p2) ∨ (((((p2 ∧ p1) ∧ True) → (True ∨ False)) ∨ p1) ∧ p5)) → ((False ∨ p4) ∨ (True ∧ (p4 → (True ∨ (p2 ∨ (p5 → p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51965605979649958683499890409 : ((((p5 ∧ (False ∨ p4)) ∧ (p2 ∧ ((True ∨ (p1 ∧ ((p3 ∧ p4) ∨ p3))) → False))) ∨ ((False → p2) ∨ ((False ∧ p3) → (p2 → p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172521573451159344340800671246 : (((p2 ∧ (p5 ∧ p2)) ∧ ((p4 → (True ∧ (((p3 → p3) ∧ False) ∧ p2))) → p1)) ∨ ((p5 ∧ ((p2 ∨ (True ∧ False)) ∧ (p2 → p1))) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_605245013011548072252106672473 : ((((p2 → (p1 ∨ (((((p1 ∧ False) → (p4 ∧ (True ∧ (((p4 → True) → p4) ∧ p1)))) ∧ p3) ∨ ((False ∧ True) ∧ p3)) ∨ p2))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219400593753453349662713264285 : ((p3 ∨ (p3 ∨ (p4 ∧ p3))) → ((False ∧ (True ∨ p2)) ∨ (p1 ∨ (True → ((True ∨ (True ∨ p1)) ∨ (((True ∧ (p3 ∨ p1)) → p4) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180424820673128627324077817985 : ((((p1 ∨ ((p5 → ((False ∨ p3) ∧ p5)) → True)) ∨ True) → (p5 ∧ p2)) → ((p5 ∧ ((p4 ∨ p2) ∨ (True ∨ (p2 ∨ p3)))) ∧ (p2 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∨ ((p5 → ((False ∨ p3) ∧ p5)) → True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 ∨ ((p5 → ((False ∨ p3) ∧ p5)) → True)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105168831147675618636251766201 : (((False ∧ (((((p4 ∧ p5) ∨ (p4 ∨ p3)) → ((p1 ∧ p2) ∨ p3)) ∨ (p4 ∨ (p1 ∧ False))) ∧ p3)) ∨ (p2 → (False → p5))) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133823829597580301193830252073 : ((((p3 ∨ p1) ∨ ((((True ∨ (((p1 ∧ (p3 → p1)) ∧ p4) ∨ ((p2 ∧ p5) ∧ p1))) ∨ True) → False) ∨ p3)) ∧ p3) ∨ ((False ∧ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626310318456796650114554169830 : ((((p3 → ((True ∧ p5) → ((((((p2 → (((p1 ∧ True) ∧ False) → p2)) ∧ p3) ∨ p4) → ((p3 ∨ p5) → p2)) ∨ True) ∨ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_620973032567917263799035214821 : (((((p5 ∨ p4) → (((p1 → (p3 ∧ (p3 ∧ ((p5 ∧ p3) ∨ p4)))) ∧ (p5 ∨ (p4 ∨ ((p5 → p4) ∨ p4)))) ∧ (p1 ∧ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168453027619763562385690586849 : (((p1 → False) → (((False ∨ ((False ∨ (False ∨ True)) ∨ (False → (p1 ∧ p2)))) ∨ p5) → p4)) → (((True ∧ p2) ∨ True) ∨ (p4 ∧ (p3 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53378854806024019609862336098 : ((((((p3 ∧ p1) → ((True ∨ p4) → True)) ∨ (p4 ∨ p5)) → p4) → (p4 ∨ ((False ∨ (False → (False ∧ (p2 ∧ (True → True))))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144768216317293787924389223916 : ((((p5 ∨ ((p1 ∨ (p3 ∨ p1)) ∨ ((False ∨ p3) ∨ p4))) → (p2 ∨ (p4 ∧ False))) ∨ ((False ∧ True) → p1)) ∧ ((p4 ∧ (True ∧ p5)) → p4)) := by
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
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65502187939340326700394443057 : ((p3 ∨ (p5 ∧ (p1 → (((True ∨ (p4 ∧ p1)) ∧ (p3 → (((False ∨ False) ∨ ((False ∧ (p3 ∨ p4)) → (p3 ∧ False))) ∧ False))) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158715638260029890494148416032 : ((p3 ∧ (((p5 ∧ (p3 ∧ ((False ∧ p3) ∨ p1))) ∨ (False → (p5 ∧ (p1 ∧ p5)))) ∨ (p3 ∨ True))) ∨ ((p1 → True) ∨ (p5 → (p3 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168093171213352107989953758050 : ((((p2 ∨ (p4 → p5)) ∨ True) ∨ (p2 ∧ ((p5 → (p2 → True)) ∨ ((p5 ∧ p2) ∧ True)))) → ((p4 ∧ p5) ∨ ((True ∨ p4) ∧ (p5 ∨ True)))) := by
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
      case inr h5 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
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
      -- True on the right can always be proven directly.
      apply True.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165648099242269508073068258413 : ((((p3 ∨ (p3 ∨ (False ∧ p4))) ∧ False) ∨ ((p1 ∧ (p3 ∧ (p3 ∨ (p4 → p4)))) ∨ p3)) ∨ ((((False ∧ p2) ∧ p5) ∨ (p4 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38955594662258659527873924998 : ((((p5 ∨ (p4 ∧ p2)) → ((True → (True ∧ (((p2 → ((True → p4) ∨ (p5 ∧ (True ∧ True)))) ∨ (p4 ∨ p2)) ∧ p5))) → p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62920574561507067552932503663 : ((p4 ∧ (False ∧ (((p1 ∨ ((p4 ∨ p5) → (True ∧ (p5 → ((p1 ∨ False) → (p4 ∧ p2)))))) ∧ p3) → (p1 ∨ (p2 ∨ (False → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_103231894361967797875196375142 : (((p2 ∧ (p2 ∧ (p5 → ((((p5 ∨ False) → ((False → p1) → False)) ∧ ((((False ∨ p1) ∧ p1) ∨ p3) → p1)) ∧ True)))) ∨ True) ∧ (True ∨ p3)) := by
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
theorem thm_5_vars_313025621311334027236955046582 : (p3 ∨ (((True → ((False ∨ (p4 ∧ False)) ∧ (p5 → (p2 ∨ (p1 ∧ ((p1 ∧ ((p1 → (p5 → (p3 ∧ p2))) → p2)) ∨ False)))))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76829749470841592560759336359 : (((((False → (((((p4 ∨ False) → p4) ∨ p2) → p4) ∧ True)) ∨ p2) → ((((True ∧ False) → p2) → (p3 ∨ False)) ∨ (False → p1))) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → (((((p4 ∨ False) → p4) ∨ p2) → p4) ∧ True)) ∨ p2) → ((((True ∧ False) → p2) → (p3 ∨ False)) ∨ (False → p1))) := by
    -- Implications on the right can always be decomposed.
    intro h3
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264280119849354551890920697417 : (True ∧ ((p5 ∧ (False ∨ ((p1 ∨ p5) ∨ p3))) ∨ ((p2 → p2) → (((p4 → (p4 → (False → p2))) ∨ p3) ∧ (p2 → (True ∨ (p3 → True))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224715174794852990030271759953 : ((p3 → (p2 → p2)) ∧ (p3 → (((p1 ∧ (p1 ∧ (p1 ∨ ((True ∧ ((p2 ∨ ((p3 ∧ (p3 → p2)) → p3)) ∧ p5)) → False)))) ∨ False) ∨ p3))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160072831839963721463740721887 : (((p5 ∧ (p1 → ((True → (((p1 ∧ p2) ∨ p1) → (True ∧ ((p4 ∧ False) ∧ p3)))) → p1))) → False) → ((True → p5) → ((p2 → p4) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∧ (p1 → ((True → (((p1 ∧ p2) ∨ p1) → (True ∧ ((p4 ∧ False) ∧ p3)))) → p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : (p5 ∧ (p1 → ((True → (((p1 ∧ p2) ∨ p1) → (True ∧ ((p4 ∧ False) ∧ p3)))) → p1))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h12
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41875367999951389632000728878 : ((((False ∧ (True ∨ False)) ∨ ((((((False → p4) ∧ (p5 → p5)) → (p1 ∨ p5)) ∧ (p2 → True)) ∨ ((p1 ∨ p2) ∨ p4)) ∨ True)) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114313023578543463882606275941 : (((((p4 ∧ p1) ∨ (True → p1)) ∧ (p2 ∧ (p2 ∨ (True ∨ (((p5 ∨ p5) → True) → p5))))) ∧ (((True → p5) ∧ p2) → True)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158983488569865309427743331882 : ((p3 ∨ ((False ∨ (p1 ∧ ((p3 ∨ p3) ∨ (p2 → p4)))) → (((p5 ∧ (p5 ∨ True)) → p2) ∨ True))) ∨ (False → (((p5 ∨ p1) ∧ p2) ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180089107383726703110828249382 : (((((p2 ∧ (p5 ∨ ((True ∨ False) ∨ True))) ∧ (p1 → p4)) ∧ p1) → p5) → (p3 → (((p1 → (p2 ∧ p1)) ∨ p4) ∨ ((True → p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249058909710936956912822842191 : ((p4 ∨ p1) ∨ (((((p4 → p4) → True) → (p2 → ((p2 ∧ (((p4 → p2) ∧ p5) ∧ True)) → p4))) ∨ ((p1 ∧ False) → True)) ∨ (p4 ∨ p1))) := by
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
theorem thm_5_vars_181720088208635670798072931378 : ((p5 → (p5 → (p3 → (((True ∨ (p2 ∨ True)) → (True ∧ p3)) → False)))) → (((p3 ∧ False) ∨ ((p1 → False) ∧ p1)) → ((False → True) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114120631843083466917519921594 : (((True → (False ∨ ((p2 ∨ (((True ∧ ((p5 → p4) → (False ∨ p2))) ∧ p2) ∧ p2)) ∨ (p1 → p1)))) ∨ (p4 → (p4 ∧ False))) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133745271283172211658118961503 : ((((p2 → ((p4 → ((True ∧ True) → False)) ∧ False)) ∧ (p1 ∧ (((p3 → (True ∨ p3)) ∨ (p3 → p1)) → False))) ∧ False) ∨ (True ∨ (p3 → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342603531903250285550315016518 : (p2 → (((((p3 → p1) ∨ p2) → p3) ∧ (((p1 ∨ p3) ∧ p5) ∨ p3)) → ((((p1 ∨ p1) → p3) ∨ (((p2 ∨ p1) ∨ False) ∧ p4)) ∧ p3))) := by
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
    cases h6
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : ((p3 → p1) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h15
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  case inr h18 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  -- Conjunctions on the left can always be decomposed.
  let h22 := h2.left
  let h23 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h28 : ((p3 → p1) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h29 := h22 h28
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- One of the premise coincides with the conclusion.
    exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106706805388555022490697869386 : ((((((p5 ∨ p5) ∨ p4) ∧ True) ∨ False) ∨ (p1 ∨ ((False ∨ True) → ((((p3 → (True ∨ (False → False))) ∨ p3) ∨ p1) ∨ p1)))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161044495968614180512996359142 : ((((False ∧ p1) → p2) → (p3 ∨ (p3 → ((p4 ∧ (((p4 → p3) → True) ∨ p3)) ∨ (p5 ∨ False))))) → ((p3 ∧ ((p3 ∧ p2) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633596241972504059650691323803 : ((((((False ∨ (p5 ∨ p1)) ∧ (((p4 → (p3 → (p4 → p4))) ∧ (p5 ∨ (p5 ∧ p2))) ∨ (True → (p1 ∧ False)))) ∨ (True ∧ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198768414126837255498794371263 : ((True → (p2 ∨ (((p1 ∧ p1) ∨ p2) ∧ True))) ∨ ((True → ((False → p1) ∧ (p4 ∨ (((True ∨ (p2 ∨ False)) → (True → p3)) → p1)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69153277424708646293765001025 : ((p5 → ((((((p3 ∧ False) ∨ False) ∨ ((((p2 ∨ p5) → p4) ∧ False) ∧ p2)) ∧ p2) ∧ (p2 ∨ p2)) ∧ (((False → p2) ∨ p2) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673807556454309264660126248753 : (((((p2 ∨ False) ∨ (p1 ∧ (((((p1 ∨ (((False ∨ p3) ∧ p2) ∧ (p4 ∨ True))) ∨ p1) ∨ False) → False) ∧ p1))) → ((p3 ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351525720713070287858889816461 : (p4 → (((p3 → (((p5 ∨ (p2 → p2)) ∨ (p4 ∨ False)) ∨ (((p5 ∨ True) ∨ p4) → p1))) → p2) ∨ (p4 ∨ ((False → p1) ∨ (p1 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118715019916932057705903715752 : ((p5 ∨ (((((((p4 → p5) → (p5 ∧ p3)) → p2) ∧ ((p2 ∧ p5) → p1)) ∨ ((p4 → p1) ∧ False)) ∨ p5) ∨ (p1 ∧ p1))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784183717546198335259351188773 : (((p3 ∨ ((True → p5) → (p5 ∧ (p3 ∧ (((p5 ∨ ((p2 ∨ p2) → False)) → ((p3 ∧ ((p4 → p2) ∧ p2)) → p3)) → (False ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665369729815573250351123204496 : (((((p3 ∧ ((p1 ∨ (False ∨ ((((p1 → (p1 ∨ ((p2 → p5) → False))) → p2) ∨ p5) → p4))) ∨ True)) ∧ p4) ∧ ((p2 → p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340831925087731714294693762058 : (p2 → ((((((((True ∨ p4) ∧ False) ∧ p1) ∨ (p2 → p5)) ∨ (((p4 ∧ p4) → (p4 → True)) ∧ True)) ∧ (True ∨ False)) → (p1 ∧ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37490240274405188497222334122 : ((((((False → p2) ∧ p2) ∨ ((p2 ∨ p4) → (p4 ∧ (p2 ∨ (((p1 → (False ∨ p3)) ∨ (p5 ∨ p5)) ∨ (False → p5)))))) ∨ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171773138776203009363880265753 : ((((p5 ∨ (p1 ∨ ((False → ((True → (p4 ∨ p1)) ∨ p5)) ∧ p2))) → p3) → p4) ∨ (p5 ∨ ((((p3 → p4) → p3) ∨ (p4 ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600699261382180845776325725326 : ((((False ∧ (((p4 ∨ (((p4 ∨ (p5 ∧ (p1 → (p2 ∨ (p2 ∧ p1))))) → p5) ∨ p2)) → (False → (False → p4))) → (p4 → p2))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115681326813323593816766792127 : (((p5 ∧ (((True → p2) ∧ True) ∨ p1)) ∨ (((((((p1 ∨ p5) ∧ p4) → False) ∧ p1) ∧ p4) ∧ (p5 ∨ p1)) ∨ (p5 ∨ True))) ∨ (p5 → p5)) := by
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
theorem thm_5_vars_44693490457109008581365586497 : (((((p4 ∧ (False ∨ p2)) ∧ p2) ∧ ((p1 ∨ (True ∧ ((p5 ∨ p4) ∧ (p1 ∧ p3)))) ∨ ((p1 ∧ p3) → (p5 ∨ (True → p1))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164970358533052127685679140393 : (((((p1 ∧ (p4 ∧ (p1 ∧ (p2 → ((p1 ∨ True) ∨ p2))))) → p4) ∨ (p4 ∨ p4)) → p2) ∨ (p3 → (((p3 → p2) → (False → False)) ∨ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205869283483372826948511984712 : ((True ∧ (((p4 ∨ p5) ∨ p2) ∧ p5)) ∨ ((((p5 ∨ p2) ∧ (((True ∧ p4) ∧ (p3 ∧ True)) ∨ (False ∧ True))) ∧ (p4 ∧ p3)) → (p1 ∨ True))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Conjunctions on the left can always be decomposed.
      let h25 := h22.left
      let h26 := h22.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h3.left
      let h28 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187327407091235194071772808372 : ((p2 ∧ ((((p4 ∨ True) ∨ ((p2 → True) ∨ True)) → True) ∨ p5)) → ((((p2 ∨ (True → p4)) ∨ p2) → (p3 ∨ p2)) ∨ (True ∨ (p4 → p5)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186054995959382231274658455813 : (((((p4 ∨ ((p1 ∨ p3) → (p3 ∧ p2))) → True) ∨ False) ∨ True) → ((True → p1) ∨ (((True → p4) ∧ p1) → (p3 → (p5 ∨ (p3 ∨ p2)))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42670038805030605383701753530 : (((p4 ∨ ((p4 ∨ False) ∨ ((((((p1 ∨ (p4 ∧ p2)) → (p5 ∨ (False ∨ p2))) ∧ (p2 ∧ (p5 ∧ p2))) → False) ∨ p5) ∧ p4))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234695693960399697672152726905 : ((p4 → (True ∨ p2)) → (((False ∧ ((((False ∧ (False ∨ p2)) ∧ p3) → p3) ∧ (False ∧ p2))) ∨ ((False ∧ (p2 ∧ p2)) ∨ True)) ∨ (p5 ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254055712098681889091281543945 : ((p2 ∧ True) → ((((p4 ∨ p3) ∨ p2) → p5) → (((((p3 ∨ p1) ∧ ((p4 → ((p4 ∧ p5) → p2)) ∧ p4)) ∨ (False ∨ p2)) ∧ p5) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p4 ∨ p3) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137296850728084056280059754492 : ((p2 ∧ ((False ∨ ((((True → (True ∧ p1)) ∨ ((p2 ∨ (p3 → p2)) ∨ ((p4 ∨ False) ∨ p4))) → False) ∨ p3)) → p4)) ∨ (p5 ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165344312139728755205742243890 : (((((p4 → True) → p3) ∧ (((True ∧ (True ∧ p1)) → True) → p1)) ∧ ((True ∨ True) → p3)) ∨ ((False ∧ (False → (p5 ∧ (p5 ∧ p3)))) → p5)) := by
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
theorem thm_5_vars_247635147413188335810176130747 : ((False ∨ p5) ∨ (p3 ∨ (((p4 ∧ (((True ∨ (p5 → p1)) ∨ p5) → ((p2 ∧ p3) → p4))) ∧ ((p4 ∧ p5) → ((p5 ∨ p1) ∨ p1))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240474154676474817485550917710 : ((p5 ∨ True) ∧ (p2 → (((p4 ∨ ((p3 ∨ (p2 ∨ (True ∧ False))) ∧ p1)) ∧ p5) ∨ (((True → p4) ∧ ((p3 ∨ (p2 → p1)) ∧ p5)) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659295939258986113565595665194 : ((((p5 → (((((p2 → p1) ∧ p5) → (p5 ∧ p4)) ∧ ((False ∨ (p1 → p3)) ∨ (p5 ∧ (p3 → p1)))) ∨ (True ∨ p5))) ∨ (False → p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_147768149942808126780341025066 : ((((False → p2) ∧ ((p2 ∧ ((p2 → ((p2 ∨ p3) → False)) → (p4 → (False ∨ p4)))) ∧ (p3 → p1))) → p2) ∨ ((p1 ∨ (p3 → p5)) ∨ p4)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186653215901514333228369260830 : ((((((True → True) → p1) → True) ∨ p2) ∧ (p2 ∧ (p5 → p2))) → (p3 → (((p5 ∧ p2) ∧ p1) ∨ (True ∧ (p1 ∨ (p4 ∨ (p4 ∨ p2))))))) := by
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
    let h6 := h4.left
    let h7 := h4.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52849682220274799062908318747 : ((((p5 → True) ∨ (p2 ∨ ((True ∨ p3) ∨ ((p2 → (False → p3)) ∧ p2)))) → ((p4 ∧ p2) ∨ (False ∧ (p5 ∧ (False ∧ (p1 → p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256104448857790774509174750221 : ((True ∨ p5) → ((p2 → (False ∨ (((p5 ∨ True) → ((((True ∨ p2) → p5) ∨ p4) ∨ p4)) ∨ ((p2 ∧ (p1 → p2)) ∧ p1)))) ∨ (True ∨ True))) := by
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
theorem thm_5_vars_4134100167331905717288788535 : (p3 ∨ (p1 → ((((((True ∨ p3) ∨ (p3 ∨ False)) → False) ∧ (((p5 ∨ (True → p1)) ∨ (p4 ∧ (True → p4))) ∨ p2)) → p4) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : ((True ∨ p3) ∨ (p3 ∨ False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : ((True ∨ p3) ∨ (p3 ∨ False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h12 := h3 h11
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : ((True ∨ p3) ∨ (p3 ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h18 := h3 h17
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240447058882198913605793703547 : ((p5 ∨ True) ∧ ((((p1 → p1) ∧ ((True ∧ (False ∨ p3)) ∧ p3)) ∧ p5) ∨ (((p2 → ((False ∨ False) ∨ (True ∧ (p1 ∧ False)))) ∧ p5) → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617041349188538109115570810681 : ((((((False → (False → (p1 → p4))) → (True → p1)) ∧ ((p4 ∨ p4) ∧ (((((True → True) ∧ True) ∨ p2) ∨ p4) → (p3 → p5)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631124631712574908232092620446 : ((((((p4 ∧ ((p2 ∧ ((((p5 ∨ ((p2 ∧ p5) ∨ ((p5 → p2) → (True → p2)))) → p5) ∧ p1) ∨ p1)) ∨ False)) ∨ p5) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165754454781395356948035901366 : (((False ∨ ((p1 ∨ p4) ∧ p3)) ∨ (p4 ∨ (False → (((p1 ∨ (p1 ∨ p5)) ∨ False) → p1)))) ∨ (p2 ∨ (p3 ∨ (p3 ∧ ((p1 → p1) → p2))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h1
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137485694474406031969445514865 : ((p5 ∧ ((((False ∨ (p3 ∨ (((p1 ∨ True) ∨ (p3 → False)) → (p3 → (p3 ∧ p1))))) → p5) ∧ (p5 → p2)) ∨ False)) ∨ (False ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861625584261292642502150765647 : ((((((p5 ∧ (p2 ∨ (p4 ∧ ((True ∧ (p2 ∧ (p2 → True))) ∨ p2)))) ∨ (((p4 ∨ p3) ∧ p2) ∧ p4)) → (p1 ∨ (True ∨ p3))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ (p2 ∨ (p4 ∧ ((True ∧ (p2 ∧ (p2 → True))) ∨ p2)))) ∨ (((p4 ∨ p3) ∧ p2) ∧ p4)) → (p1 ∨ (True ∨ p3))) := by
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
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h18.left
      let h21 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h2
  -- False on the left can always be used.
  apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214491129008435157922097223198 : (((p2 ∧ False) ∧ (p1 ∧ False)) ∨ ((p4 → (p5 ∨ p4)) ∨ ((((p2 ∧ p1) → p2) ∧ ((True → True) → p5)) ∨ ((p4 → False) ∨ (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593978805377535661120796658739 : ((((((p2 → False) → (((p2 → ((True → p4) ∧ (p1 ∨ (p4 → True)))) → (p1 ∨ True)) → p2)) ∨ ((p1 → p5) → (True ∧ True))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54002320027287047257509539809 : ((((((p1 ∧ p5) → (False ∨ (p1 ∧ p3))) ∨ p2) → False) → (p5 ∨ ((p4 ∧ ((False → p2) ∨ (p1 ∧ p4))) → (p2 → (p4 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765685248950148568030705393230 : (((p4 ∧ ((p4 ∧ ((p4 ∨ ((True ∨ (p2 → p5)) ∨ False)) ∨ (p4 ∨ p2))) → ((True ∧ ((((True ∨ p3) ∨ p4) ∨ p1) ∧ False)) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167799704235100967425245398127 : (((((False → p1) ∨ (((p5 ∨ p3) → p5) ∨ p2)) ∧ True) ∧ ((p4 → p4) ∧ (True → False))) → (((p5 ∨ (p4 → p5)) ∧ p2) → (p3 → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h8.left
      let h13 := h8.right
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h8.left
        let h19 := h8.right
        -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
        have h20 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h19, we can now drive its conclusion.
        let h21 := h19 h20
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h8.left
        let h24 := h8.right
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h26 := h24 h25
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h1.left
    let h29 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h28.left
    let h31 := h28.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Conjunctions on the left can always be decomposed.
      let h33 := h29.left
      let h34 := h29.right
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h36 := h34 h35
      -- False on the left can always be used.
      apply False.elim h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h29.left
        let h40 := h29.right
        -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
        have h41 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h40, we can now drive its conclusion.
        let h42 := h40 h41
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h29.left
        let h45 := h29.right
        -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
        have h46 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h45, we can now drive its conclusion.
        let h47 := h45 h46
        -- False on the left can always be used.
        apply False.elim h47



