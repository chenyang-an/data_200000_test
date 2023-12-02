variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137444531830774262841387472328 : ((p4 ∧ ((p1 → ((p2 ∧ ((True ∧ p4) ∧ (p1 → p2))) → True)) → (((p1 → p4) ∧ ((p5 ∧ p3) → False)) ∧ p4))) ∨ (p1 → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214590630367111260014359693147 : (((p4 ∨ False) ∧ (p5 ∧ p1)) ∨ (((p3 → (((p3 → False) → p2) ∧ True)) → p4) → (((p5 → ((p3 ∨ p3) ∨ True)) ∧ (p3 ∨ p1)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (((p3 → False) → p2) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301782914552889240539359814775 : (False ∨ ((p1 ∧ p4) ∨ ((((((p2 ∨ (((True → p3) ∧ p3) ∧ p1)) ∧ False) ∨ True) ∧ (p5 ∨ (p4 → (p3 → (p2 ∨ p1))))) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614066674244574344124489175493 : (((((p4 ∧ ((p1 ∧ ((p1 ∧ (p3 ∧ (p1 ∧ ((p3 ∧ (False ∨ True)) → (p1 ∨ False))))) → True)) → p4)) ∨ ((p3 → p5) ∧ p4)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_159016931807957447089597000386 : ((p4 ∨ ((((((p5 ∨ p3) ∧ p2) → p4) → ((p3 ∨ p1) ∨ p5)) ∧ p1) ∨ ((p5 → p5) ∧ p2))) ∨ (((False ∧ p5) ∧ (False ∨ p3)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47740828844758429141733254577 : ((((((((p5 ∨ True) ∨ (p1 ∨ (p3 ∨ False))) → p3) ∨ False) ∨ (p3 ∧ (((p4 ∧ (False ∨ p2)) ∨ p1) ∧ False))) ∨ p2) → (p1 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60090744373507325778515444481 : (((p3 ∨ True) → (p3 ∧ (((p3 ∧ ((p3 → (((p5 ∨ (True ∨ p2)) ∧ (p4 ∧ (p4 ∧ p2))) ∨ p4)) ∧ p2)) ∧ p3) → (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252143715054090329046760017778 : ((p4 → p3) ∨ (((p2 → ((((False → (p2 → False)) ∨ (((p2 ∧ p2) → False) ∨ p2)) → ((p3 → False) ∨ False)) ∨ (p2 ∨ p2))) ∨ p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185464956286113585754779865744 : ((p1 ∨ ((p2 → (False ∧ ((p3 ∨ (p5 ∧ p5)) ∧ p4))) → p2)) ∨ (False → (p3 → (p3 → ((True ∧ (p1 ∧ p2)) ∧ ((p1 ∨ p2) → p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57820187097356398624447466670 : (((p3 ∧ (True → True)) → (((((p5 → (p3 ∨ ((True → ((p1 → (True ∨ False)) → (p2 → True))) → True))) ∨ p1) → p5) → False) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39159961755969930683201097739 : ((((p3 ∨ p2) → ((p2 → ((p2 → p3) ∧ (True → ((p1 ∧ (False ∨ (((p4 ∨ (p4 → p5)) ∨ True) ∧ p2))) → False)))) ∧ p3)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670250279042993026281141086513 : (((((((p5 ∨ p3) ∨ p2) ∧ p5) → ((((p1 ∧ (True ∧ False)) ∨ (p5 ∨ (p5 → False))) → (p5 ∧ p4)) → p4)) ∨ ((True ∧ False) ∧ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : ((p1 ∧ (True ∧ False)) ∨ (p5 ∨ (p5 → False))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p1 ∧ (True ∧ False)) ∨ (p5 ∨ (p5 → False))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : ((p1 ∧ (True ∧ False)) ∨ (p5 ∨ (p5 → False))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h16 := h2 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171463419938653221969156716502 : (((False ∨ ((((p5 ∧ ((p3 → False) ∧ p2)) ∨ False) ∨ (p2 ∧ p4)) ∧ True)) ∧ True) ∨ ((True → (((p5 ∨ (p5 ∧ p3)) ∨ True) ∧ False)) → p2)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168475808842926666758443209190 : ((True ∧ ((((True ∧ (p4 ∨ (True ∧ (p4 ∨ (p4 → False))))) ∧ p2) ∨ (p5 → True)) → p5)) → ((True ∨ ((False ∨ (p2 ∨ p4)) → p5)) → p5)) := by
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
    have h6 : (((True ∧ (p4 ∨ (True ∧ (p4 ∨ (p4 → False))))) ∧ p2) ∨ (p5 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : (((True ∧ (p4 ∨ (True ∧ (p4 ∨ (p4 → False))))) ∧ p2) ∨ (p5 → True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204853145517134806758542183559 : (((((False ∨ p3) ∨ p5) → p4) → p5) ∨ (((False ∧ p2) ∧ (((p4 → p5) → ((p4 ∧ ((True → p2) → False)) → (p5 → p1))) → p1)) → p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244576835073232820168688220382 : ((False ∧ p4) ∨ (((((True → p4) → p3) ∨ p2) ∧ (p5 ∧ (p2 → p5))) ∨ (p3 → (True ∧ (((p1 ∨ p4) → (p4 ∧ p2)) ∨ (p3 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173167748645265683489610197696 : ((p4 ∨ (((p2 ∧ ((p1 ∨ (p3 → (False → (p1 ∨ True)))) ∧ False)) ∧ p1) ∨ p4)) ∨ (((p1 ∨ True) → (((p4 → p5) ∨ True) ∧ False)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54146998519261864375991413834 : (((False → (p1 ∧ (True ∨ (((p4 ∨ p1) ∨ p4) → p1)))) → (((p3 → ((((p2 ∨ p1) ∧ p4) ∨ False) ∧ p5)) ∨ p4) → (p3 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755582485719552543858352553020 : (((p1 ∧ (((((True ∨ (True ∧ p2)) ∨ (p1 ∨ (p4 ∨ ((p2 ∨ (p5 ∨ False)) ∧ (p2 ∨ ((p1 ∨ False) → p4)))))) → p2) ∨ True) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165062630784048052608993990276 : (((p1 ∧ ((p1 ∨ (((False → (p2 ∧ p3)) ∧ (p1 ∨ (p2 → p1))) → False)) → p2)) → p5) ∨ (((True → False) → True) → ((False ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313656752606831325739353943200 : (p3 ∨ (((True → False) ∧ (((((((True ∨ (p3 ∨ False)) → (True ∨ (p3 ∧ (p1 ∧ (p3 ∨ p5))))) → p5) → p1) ∨ p1) ∨ p2) ∨ p3)) → p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h7 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h7
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h10
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308457552852875780781895718815 : (p2 ∨ (((((((((((p5 → (p2 → False)) → (p5 ∧ False)) → p2) ∧ (False ∨ False)) → p5) ∨ p4) ∧ p4) → p5) ∨ True) ∨ (p5 ∧ False)) ∨ p4)) := by
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
theorem thm_5_vars_815491867384741159494638793736 : (((((True → (((p1 ∧ (True ∧ ((((p5 ∧ p3) ∨ p2) ∧ (True → (((True ∨ p4) ∨ p5) → p4))) ∧ p4))) ∧ p2) ∧ p2)) ∨ p2) ∧ p1) → p2) ∧ True) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179114964002926593045466942491 : ((False ∧ (p2 → (((((False ∨ p1) ∨ False) ∨ False) ∧ p5) ∨ (p5 ∨ p1)))) ∨ ((False ∨ (False → (p1 → (((p4 ∧ p2) → False) ∨ p4)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55494942766620208180976695801 : ((((p4 ∧ (p1 ∨ p3)) → (p5 ∧ True)) → (((p2 ∧ p5) → p1) ∨ ((p1 ∨ True) ∧ ((p3 ∧ ((p3 → p3) → (p5 ∨ True))) → p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673964804687191193988597939741 : ((((True ∧ ((p2 → (p3 ∧ (p1 ∨ p2))) → (p4 ∧ (p3 → (p2 ∨ (p2 ∨ (((p2 → p2) ∧ p5) → p1))))))) → (p1 ∧ (p4 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172548332775395732272204078629 : ((((p4 ∨ p5) ∨ False) ∨ ((p5 ∨ (((p4 ∨ p5) ∧ p2) → (p4 ∨ p5))) ∨ False)) ∨ (p2 → ((p4 ∨ ((True ∧ (p5 ∨ p2)) → p5)) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23243043571284878853249524857 : (((False → (((False ∧ p4) ∨ False) ∨ p5)) → (((True ∧ p2) ∧ (p3 ∧ ((p4 → p3) → ((p1 ∧ True) ∨ p3)))) ∨ ((p3 → p3) ∨ p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193944205683117346814492924823 : ((p2 ∨ ((((p4 ∧ True) → p2) ∨ False) ∧ (p1 ∧ p2))) → (((p3 ∧ ((True → p3) ∨ (True → p3))) ∨ (p5 ∧ (False → p3))) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117643082403418774260318099011 : ((p3 ∧ (((True ∧ (p5 ∨ ((True → True) → ((p4 ∧ p5) → p2)))) ∨ ((p1 ∨ p2) → (((True ∧ p5) ∧ p1) ∧ p2))) → p3)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85724175986464222377856725253 : (((((True ∧ p5) ∨ (((p4 ∧ True) → p2) → (False → p5))) ∨ p5) → ((p2 ∨ (p5 ∧ (False → (((True ∨ False) ∧ p1) → p2)))) ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((True ∧ p5) ∨ (((p4 ∧ True) → p2) → (False → p5))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689471924083408460719917923353 : (((((p2 → ((False ∧ ((p3 ∧ (p3 ∨ True)) → p4)) ∧ p3)) ∨ (p4 → (p2 ∨ p3))) ∨ (p4 ∨ (p5 → (p4 → ((p1 → p5) ∧ p5))))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177649063097633584606988210414 : ((((((p4 ∧ p5) ∧ (True ∧ ((p2 ∨ p2) ∨ p4))) ∨ p3) ∨ p5) ∧ p5) ∨ (True → (((p5 → ((False ∧ (p5 ∧ False)) → p2)) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614506973826112774204779719073 : ((((((((p2 → p5) ∨ (((p1 ∨ (True ∨ p3)) ∨ (False ∧ False)) ∧ p5)) ∧ True) ∨ (p4 ∧ p2)) ∧ (p4 ∨ (p1 ∧ (p5 ∨ p5)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45241550931835528607813041020 : (((p1 ∧ ((p2 ∧ ((p3 ∨ (p1 ∨ p1)) ∧ ((((False ∨ p5) ∨ p4) ∧ (p5 → p2)) ∨ p4))) ∧ (p3 ∨ (False → (False ∧ p4))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737607524665213923700520111333 : ((((p5 → p2) ∧ ((True ∨ ((p4 ∨ ((p2 ∨ True) → p3)) ∨ ((False ∧ (p4 ∧ (False → p4))) → (False ∨ (p5 ∨ p2))))) → (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59621860574066598688136008550 : (((p5 → False) ∨ (((((((p1 ∧ p5) ∧ False) ∧ (p5 → True)) ∧ p2) ∨ (((p4 → True) ∧ p5) ∨ p2)) → p2) → ((p4 ∧ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157853997277298969508626879202 : ((((p2 → (p3 ∨ p3)) → (p5 ∨ ((False ∨ p5) ∧ p5))) ∧ ((p1 ∨ (p3 ∨ (p3 ∨ p5))) → p4)) ∨ ((True → (False ∨ (p4 → True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303836339469718312280984565703 : (p1 ∨ ((((p2 → (True → (((p4 ∨ ((p1 ∧ (True → (p3 ∨ p4))) ∧ False)) → ((p5 ∨ True) → p5)) ∨ p1))) → False) ∨ (p5 → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142179955643587878316063780417 : ((p1 ∧ ((((True → True) → ((((p4 ∨ ((p4 ∧ p5) → (False → (False → p2)))) ∨ p2) ∧ True) ∧ p3)) ∨ True) ∨ p3)) → (True ∧ (p2 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
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
theorem thm_5_vars_213287103995829340653896813408 : ((((p2 → p4) → False) ∧ False) ∨ ((p5 ∨ ((p1 ∧ (p5 ∨ (((False ∧ p4) ∨ p2) ∨ p1))) → (p5 ∨ (p4 → (p5 ∧ p2))))) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92369391506574384760306636843 : (((p1 ∨ True) → ((p4 ∧ ((((((p3 → (((p4 ∨ False) ∨ p2) → p3)) ∨ p2) → (False → p1)) ∧ p3) ∨ p5) ∨ (p1 ∧ p4))) ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42823517704101012881386811186 : (((p1 → ((p5 ∧ ((p3 ∨ False) ∨ False)) ∨ ((False ∨ False) ∨ ((p4 → ((False ∧ p3) → p5)) ∨ (p4 ∨ ((p3 ∨ True) ∨ p5)))))) ∨ False) ∨ p3) := by
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
theorem thm_5_vars_40832161101663560350655996034 : ((((p1 → ((False ∧ (p4 ∨ False)) ∨ (p2 ∨ ((((((p1 ∧ p1) ∧ (True → False)) ∨ p1) ∧ p3) ∨ (p2 → p1)) ∨ p4)))) → p1) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187016330926564716763564519449 : (((p4 ∧ (p1 ∨ p2)) → (((p2 → p3) ∨ False) → (False ∧ p5))) → ((True ∧ (p4 → ((((p4 ∨ p3) → p3) ∧ p2) ∧ True))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213599932862927987892285680309 : ((((p3 → p5) ∧ False) ∨ p3) ∨ ((p1 ∧ (p3 ∧ (True ∧ (((p4 → False) ∧ True) ∨ p3)))) ∨ (p2 ∨ (True → ((p4 → (p1 ∧ p1)) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785435613194757782875496124267 : (((p4 ∨ (((True → ((((p4 ∨ p1) ∨ p3) ∧ (False ∧ p4)) → (p4 → (p2 → p1)))) → (((True → p2) → p5) → (True → p3))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115547016505663830988670693427 : (((p4 → (((p2 ∨ (p5 ∧ False)) ∨ p2) ∨ True)) → ((((True ∧ ((((p5 ∨ p2) ∨ p5) ∨ False) ∨ True)) → False) → p3) ∧ p5)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118732801268752124876836777701 : ((p5 ∨ (((False → (p1 ∧ False)) → (False ∧ ((False ∧ (p1 ∨ True)) ∧ (True → p3)))) → (p5 ∨ (False ∧ (p1 ∧ (p5 ∨ p4)))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62436561107895116441732543320 : ((p3 ∧ (((p2 → p3) ∧ p1) ∧ ((p4 ∨ (False ∨ (p2 → (((p2 → p2) ∨ ((p1 → False) → (p4 → False))) → p3)))) → (p4 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37903755254011013417435459851 : ((((((p4 ∨ True) ∨ ((True → ((True ∧ p3) ∧ p1)) → ((True → p4) ∧ (p5 ∧ p3)))) → (p1 ∧ (p5 → p5))) ∧ (False ∧ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214365915859206268302794445081 : (((p4 ∨ (p1 → p4)) → False) ∨ (((p3 → (p4 ∨ True)) ∧ ((False ∧ False) → (((p2 ∧ (p2 ∨ ((p4 → p2) → p4))) ∧ p1) ∧ False))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166389171139852146360626432022 : ((False ∨ (((p2 ∨ True) → (p1 ∨ (p3 ∨ p3))) ∧ ((((p1 ∧ p4) → p1) → p1) ∨ p5))) ∨ (False → ((p1 → ((True ∨ p1) ∧ p1)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38889546275094017733665064490 : (((((p1 → p5) ∨ p2) ∨ (p2 ∧ ((p4 ∨ (p2 → p2)) ∧ (((((p4 ∨ (p4 ∧ p3)) ∨ False) ∧ p5) → (p4 ∨ p2)) → p2)))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260219813995402934505987419188 : ((p2 → p3) → ((((((False ∨ ((p1 → p2) → p1)) ∧ (False → p2)) → (p5 ∧ (p1 → ((p3 ∨ p4) ∨ (p1 ∧ p4))))) ∨ p5) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641358515102580460899047854492 : (((((p2 → p2) ∨ (((((((p4 → True) ∨ p1) ∧ ((p2 ∧ p3) ∧ (True → p3))) ∨ (p3 → p4)) → p3) → (False ∨ False)) → False)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234294208525981132976460001346 : ((False → (p5 → True)) → (((False → p1) ∧ ((p4 ∧ (p5 → p3)) ∧ True)) ∨ (p3 ∨ ((((p1 ∨ p3) ∨ True) → (True ∨ (False ∨ False))) ∨ False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585748947589640705269365313879 : (((((((p2 → ((p2 → True) ∨ p2)) ∨ (True → (p5 ∧ (((((p1 ∧ False) ∧ p3) ∨ p1) → (p3 → True)) → False)))) → p5) ∧ p3) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128352815255992393462326183273 : ((p4 → ((p3 ∧ (False → (p2 ∧ ((((False ∨ (p1 → p4)) ∨ p4) → (p1 ∨ (p1 ∧ False))) ∧ (p4 ∧ p5))))) ∨ (True → p3))) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350398215564991921251214561722 : (p4 → (((p4 → ((p1 → (((((False ∧ (True ∧ p1)) ∨ p5) ∧ p5) → p3) ∧ (True ∧ (p4 ∧ (p3 ∧ p4))))) ∧ (p3 ∧ p2))) ∧ p3) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789928986645170657652323346656 : (((p5 ∨ ((True ∧ p4) ∧ (p1 ∨ (((((p3 ∨ False) ∨ ((p3 ∨ p5) → p5)) ∧ (p3 ∨ p5)) ∧ ((p1 → True) ∧ (p3 ∧ True))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350062354450390344035932609692 : (p4 → (((p3 ∨ ((p1 → True) ∧ (((False → True) ∧ p5) ∨ (p5 ∧ ((p4 ∧ (p2 ∧ (p1 ∧ (p3 → p1)))) ∨ True))))) ∧ (p2 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116679341240713506925935581097 : (((p5 → p5) ∧ ((((((((p4 ∨ p5) ∧ p2) → p3) → (p4 ∧ ((p5 → True) ∨ True))) ∨ p1) ∨ False) → p5) ∨ (False → p5))) ∨ (p5 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148323807421431391642827248833 : (((p4 → (p1 → (((p4 ∨ ((p2 → p1) ∨ True)) → p3) ∧ ((False ∨ p3) ∧ p4)))) → ((p3 ∧ p3) → p3)) ∨ (((False ∨ p2) → p2) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50240025310930792302646811354 : ((((((((p4 → (p3 ∨ (p3 ∨ ((p5 ∧ p5) → p5)))) → p2) ∧ p4) ∧ p5) ∧ (p4 ∧ True)) → p3) ∨ ((p2 → (False ∨ p3)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124775475874323192054484835872 : (((False ∨ (p4 → (p2 ∨ False))) ∧ (((p4 ∨ p3) → (p4 → p4)) ∨ (((p1 ∨ p5) ∨ True) ∨ ((p3 ∨ p2) ∨ (p2 → p4))))) → (p1 ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
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
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251538951100731762698570812955 : ((p3 → False) ∨ ((((p5 ∨ p5) → p4) → (p3 → ((((p2 ∧ p2) ∧ p1) ∧ p1) ∧ (p2 ∧ (p4 → (p1 ∨ (p4 ∧ (p5 → p4)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655402139301553551979605879023 : ((((((((((p2 ∨ (False → False)) → p5) ∨ (p5 ∧ p1)) → p4) ∧ p3) → (True → (p1 ∨ (p5 ∧ p4)))) ∨ (p3 ∧ p4)) ∨ (True ∨ p3)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_179018666385160178503599835935 : (((True ∨ p5) → ((p5 ∧ (False ∨ (p1 ∧ ((False ∧ True) ∨ p5)))) ∨ p1)) ∨ (((((True ∨ p3) ∨ (p5 ∨ p2)) ∧ p2) → (False → p4)) ∨ p2)) := by
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
theorem thm_5_vars_159081369039207740957592830615 : ((True → (((((((p4 ∧ True) ∧ ((p4 ∨ (True ∨ p3)) → False)) → True) ∨ True) ∨ p4) → p2) ∨ p2)) ∨ (True ∧ ((False → (p5 ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136132385238753141091304891741 : ((((p3 → ((True → p3) → (False → True))) ∧ True) → (p4 ∨ ((False ∨ (p4 ∨ ((p1 ∨ p5) ∧ p4))) ∧ (False → p2)))) ∨ ((p5 → p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149904195828724405782432723646 : ((p2 ∨ (p4 → (((p5 → p5) ∧ ((p1 ∨ p1) → ((((p3 → (False ∧ True)) ∨ p2) ∧ p3) ∨ True))) ∨ True))) ∨ (((False → True) ∧ False) ∧ p4)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114409618742547635373803543354 : (((((p4 ∧ p4) ∧ p5) ∧ (False ∧ (((p1 ∧ ((p5 → p3) → p4)) → True) ∨ (p1 → p5)))) ∨ (((p4 ∨ p2) ∨ p1) → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184432897903931259813404109365 : (((((True ∨ p2) ∨ False) → (p4 → (p5 → p1))) ∧ (p4 ∧ p5)) ∨ (((p1 ∧ ((p3 → p2) ∨ p4)) ∨ p4) → (((p2 ∨ True) → p2) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h7 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h8 := h2 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : (p2 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149934729181846763085196043589 : ((p3 ∨ ((p4 ∨ (p5 → p2)) → ((((p1 → (((p2 ∧ p3) → True) → p3)) → True) ∧ (p1 ∧ p5)) ∧ p3))) ∨ ((p4 ∨ p3) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134928074237228708111569902489 : ((((((p5 ∧ ((True ∨ p4) ∨ False)) → (p1 → ((p5 ∧ p4) → (False → p4)))) → (False → True)) → p5) ∧ (p4 ∨ p5)) ∨ (p2 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735643885000455795929940759629 : ((((p5 ∨ p1) ∧ ((((p3 → p2) → (p5 ∧ (False ∧ p5))) ∧ ((True ∨ False) ∧ p4)) ∧ ((p1 ∧ (p2 ∧ False)) ∧ ((p1 ∨ p5) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263698423109411733697738124125 : (True ∧ (((p1 ∧ ((p5 ∧ True) → p4)) → (((p2 ∧ (((p4 ∨ p3) ∧ p5) ∨ p1)) → False) ∨ True)) ∨ ((p4 ∧ p3) → (p4 ∧ (p3 ∧ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_806634880348945268764593427523 : (((p4 → ((p5 ∧ ((p3 ∨ ((((p2 ∧ p1) → (p1 ∧ False)) ∧ True) ∨ ((p4 ∨ p3) ∨ ((p5 ∨ (p1 ∨ False)) ∨ False)))) ∨ False)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726088088447480983815920486745 : (((((p1 ∧ p2) ∨ p1) ∨ (((p4 ∨ (p1 ∧ False)) ∧ ((True ∧ (p5 ∧ (p3 → p5))) → True)) ∧ (p2 ∨ ((True ∧ p2) ∧ (p3 → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784041539775095351030694757372 : (((p3 ∨ ((p3 → False) ∧ (p5 ∨ (p5 ∧ (((p5 → p1) ∧ (p2 ∨ True)) ∨ (((False ∧ p5) → (((p3 ∨ p1) ∧ p4) ∧ False)) → p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300665741161882765060290116259 : (False ∨ ((((p3 ∧ (p2 ∨ ((((False ∨ p4) → (p2 ∧ True)) ∧ (p2 ∧ p4)) ∨ p3))) ∨ p2) ∨ True) ∨ (p3 → (((p2 ∨ True) ∧ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161890827456087900831348380406 : ((False → (p4 ∧ ((((True ∧ p1) ∧ (p2 ∨ ((p2 ∧ p1) → (True ∧ p4)))) → (p5 ∨ p5)) → p1))) → (((True ∧ (p1 ∨ p4)) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111630580665278892633819561189 : ((((((((p1 → (p2 → p5)) ∧ p3) → (p2 ∧ True)) ∨ (p1 ∧ (p5 ∧ (p1 ∨ p2)))) → (p5 ∨ (p3 ∨ p4))) ∨ True) ∨ p5) ∨ (p5 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58959787197543300130849935316 : (((p2 ∧ p1) ∨ ((False ∨ p2) ∧ (((p3 ∨ ((((p5 ∧ p1) → p2) → (p4 ∧ p2)) → p1)) ∧ p3) ∨ ((p1 → p5) ∧ (p5 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656133832104211641955769743686 : (((((False ∨ (p3 ∧ ((False ∧ (p2 → p1)) ∧ (p1 ∨ (p1 ∨ (True ∧ p5)))))) ∧ ((p5 ∨ ((p4 ∨ p1) ∧ False)) ∨ p5)) ∨ (p2 → p2)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_63138822777518752280399660592 : ((p5 ∧ ((p1 ∧ (((p5 → ((False ∨ ((True → (p5 → p3)) ∨ False)) ∧ p3)) → (((p4 ∨ (p1 → p1)) → p3) ∧ False)) ∨ True)) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175308815683114779658289317596 : ((p4 ∨ (((False ∨ p5) → ((((True ∧ False) → False) → (p5 ∧ True)) → p2)) ∧ p1)) → ((p3 → p4) ∨ ((p4 ∨ ((p4 → True) ∧ p1)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337816867299882768941333246728 : (p1 → ((p3 → (((True ∨ (p1 → (p1 ∨ False))) → p1) ∨ ((False ∧ (False ∨ False)) → p2))) → (p3 → (True ∧ (p2 ∨ (p5 ∨ (p4 ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190872738117538832302243651761 : ((((p2 → (True → p4)) ∨ (p5 → False)) → (p3 ∨ p5)) ∨ (True ∨ ((p4 ∨ (((False → (p2 ∨ p2)) ∨ (False ∧ (True ∧ p4))) → True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164714340134149364907604107925 : (((((True → (((False ∨ p2) ∧ p4) → ((p5 ∨ (p5 ∨ p1)) ∨ p4))) ∧ True) → p5) ∨ False) ∨ (((p2 ∧ p5) ∧ True) → ((p2 ∨ p1) ∨ p2))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658513705839641689410746239594 : ((((p2 ∨ ((p2 → ((((p4 ∨ p4) ∧ (p5 ∧ False)) ∧ (True ∨ p5)) ∨ (p2 ∧ ((p5 ∨ (p5 ∨ p3)) ∨ p4)))) ∨ p1)) ∨ (p4 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636284666517443470420977138636 : ((((((((True ∨ p4) ∨ True) ∧ ((((False ∧ p1) ∧ p3) ∨ p4) ∧ (p3 → p5))) ∧ p5) → (((p1 → p4) ∧ False) → (p5 ∧ p2))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141457759904407433433450153475 : ((((False → p1) → p1) ∧ (((((False ∨ (((p2 → p3) ∧ p4) → (False → (True → p1)))) → p3) ∧ False) ∧ True) → True)) → ((p5 → p3) ∨ True)) := by
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
theorem thm_5_vars_57633501579354279938491969326 : ((((p4 ∧ False) ∨ p1) → ((((p5 ∨ (p2 ∨ ((p4 ∧ p5) → p4))) → p5) ∨ (p2 ∨ (p5 → (p3 → ((True → True) ∧ True))))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774786498632589374033600970171 : (((False ∨ (((p3 ∧ p4) ∨ (p5 ∧ (True ∨ p3))) ∨ (p3 → (((p5 ∨ (True ∧ p1)) ∧ p2) ∧ (p3 ∨ (p1 → ((True ∧ p3) → p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195455052856101750509573892515 : ((((p5 → p5) ∨ p2) ∨ ((p2 ∨ p2) ∧ p5)) ∧ ((p2 ∨ (p1 → (True ∨ ((p2 → p1) ∧ True)))) → (((p3 → p4) → p1) ∨ (p4 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308384530519298027613334098191 : (p2 ∨ ((((((((p5 ∧ (p2 → False)) ∧ (p5 → True)) ∨ False) → (p5 ∨ p5)) ∨ p1) → (p2 → (((p1 → p1) → False) ∧ p5))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257901262752992674477170724666 : ((p4 ∨ True) → (True → ((p2 ∧ (p4 ∧ p5)) ∨ ((((((True → False) → p3) → True) ∧ True) ∨ (p5 ∨ ((p5 → p4) ∨ (p1 ∧ p3)))) ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626224063792393983462190594005 : ((((p3 → ((((p2 → p4) ∨ (((p4 → True) → False) → p5)) → (False ∨ (True ∧ ((p2 ∧ p5) → False)))) ∨ ((True ∨ p4) ∨ p2))) ∨ p5) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



