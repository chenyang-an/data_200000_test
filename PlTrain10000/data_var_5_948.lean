variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305665805074935207437187995896 : (p1 ∨ (((((p3 ∨ (False → False)) ∨ p1) → (p2 ∨ p2)) ∧ False) ∨ (True ∨ ((p3 → (p1 ∧ (False → p4))) ∨ ((p5 → (p1 → False)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43946818196741106082753270422 : ((((((p5 ∨ p2) ∧ p5) ∧ (p3 → (p5 → (p4 → ((p3 → ((False → (False ∧ False)) ∧ p1)) ∧ (p4 → p4)))))) ∨ (False ∧ p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230680088644640633892139872707 : (((p4 → True) ∧ p1) → (((p3 ∧ ((((p3 → True) ∨ p4) → (p5 → (p3 → True))) ∨ p4)) → p5) ∨ (((True ∨ p2) ∨ False) ∨ (p5 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723070051910978389540340186678 : (((((p3 ∨ True) ∨ p4) ∧ (p4 ∨ ((p5 ∨ ((False ∨ (False ∨ True)) ∨ (True ∨ p1))) ∨ (((False ∨ False) ∧ ((True ∧ p2) ∧ p4)) → p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_891080478163821686960239378736 : ((((p5 ∨ (((True ∨ p1) → (p4 → (True ∨ (p1 ∧ ((p1 ∨ (p5 ∨ p5)) → p3))))) → (((False ∧ p3) ∨ True) ∨ False))) → (p2 ∧ p4)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (((True ∨ p1) → (p4 → (True ∨ (p1 ∧ ((p1 ∨ (p5 ∨ p5)) → p3))))) → (((False ∧ p3) ∨ True) ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63922399343582975927263986664 : ((False ∨ (((((True ∧ p1) → p2) ∧ ((p3 ∨ (p3 ∨ ((p3 ∨ (p2 ∨ (p2 ∧ True))) ∨ (False ∨ (p3 ∧ p5))))) ∨ p3)) ∧ p1) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658779788970457350028473435151 : ((((p5 ∨ ((p2 ∨ (False → p2)) → (((p2 → False) ∧ (((p3 ∧ p3) ∨ (p5 ∧ ((p5 ∨ p5) ∨ p3))) ∨ False)) ∨ True))) ∨ (p2 ∨ p5)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_812971024442032598714998358737 : (((((((p5 ∨ p1) ∨ p1) ∧ ((True ∧ ((True ∨ p2) ∨ (True ∧ p4))) → (p5 ∧ ((((p3 ∧ p2) ∨ p2) ∧ False) ∧ False)))) ∧ p3) ∧ p1) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (True ∧ ((True ∨ p2) ∨ (True ∧ p4))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h15 : (True ∧ ((True ∨ p2) ∨ (True ∧ p4))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h16 := h7 h15
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h20 : (True ∧ ((True ∨ p2) ∨ (True ∧ p4))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h21 := h7 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60386814991330271817643134158 : (((p3 → p3) → ((((p1 ∨ p5) → (p3 ∨ ((True ∧ p1) ∧ ((True ∨ p2) ∧ p3)))) → (p2 ∧ p3)) → ((True ∨ p2) → (p2 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695239140166914879604932002993 : ((((((((p4 ∨ (False → False)) ∧ (p2 ∧ (p3 → p5))) ∧ False) ∨ p5) → False) → ((p3 ∧ ((p1 ∨ p5) ∨ p2)) ∧ (p4 ∨ (p2 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152322416616740428525767640478 : ((((True ∧ True) → (p1 ∧ False)) ∧ ((p4 ∨ (p1 ∧ ((p1 → p5) → True))) → ((True → True) ∨ (p1 ∧ p5)))) → (p2 → (p3 ∧ (p4 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h11 := h8 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h15 : (True ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h16 := h13 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204106020959248179931447762848 : (((((p4 ∨ p5) ∧ False) ∧ p3) ∧ False) ∨ (True ∧ (p5 ∨ (False → (p2 → (p3 → (p4 ∧ (((False → p5) → p1) ∨ (p5 → (p5 → p2)))))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171627468673795237365137811292 : (((((False ∨ True) → p4) → (p1 ∧ ((((p4 → p3) ∨ p5) ∨ p1) ∨ False))) ∨ p3) ∨ ((p1 ∨ (p3 ∧ ((True → (p4 → p5)) → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165520181130949809544955087590 : (((((p3 → False) ∧ p2) ∧ (p1 ∧ (p5 → (p4 → True)))) → ((True ∨ p2) ∧ (p2 ∧ p5))) ∨ ((((True ∨ p2) ∨ (p4 → p4)) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_601628581509224743546782186372 : ((((p3 ∧ ((p3 → False) → ((p1 → (p1 → (p1 ∧ p3))) ∧ ((p3 ∨ p2) ∧ (True ∧ (False → (((False ∧ p3) ∧ False) ∨ p1))))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78429937051205586092312342310 : ((((((False → ((p5 ∧ (p2 ∨ p1)) ∨ (p3 → p4))) → (p5 ∨ ((p1 → ((p3 ∨ False) ∨ p2)) ∨ p3))) → p5) ∨ p5) ∧ (p3 ∨ p2)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((False → ((p5 ∧ (p2 ∨ p1)) ∨ (p3 → p4))) → (p5 ∨ ((p1 → ((p3 ∨ False) ∨ p2)) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h6
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : ((False → ((p5 ∧ (p2 ∨ p1)) ∨ (p3 → p4))) → (p5 ∨ ((p1 → ((p3 ∨ False) ∨ p2)) ∨ p3))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h10
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322763407370819314164228843568 : (p5 ∨ ((((p1 ∧ (p5 ∨ (p4 → (p5 → ((p5 ∨ ((p2 → False) ∨ (p2 → (p3 → p5)))) ∨ (p5 ∨ p5)))))) ∨ True) → (True ∧ p2)) → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p5 ∨ (p4 → (p5 → ((p5 ∨ ((p2 → False) ∨ (p2 → (p3 → p5)))) ∨ (p5 ∨ p5)))))) ∨ True) := by
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
theorem thm_5_vars_685294588468212720202339601054 : ((((p2 → ((p4 ∨ (((p4 → (True ∨ (p5 ∨ p1))) ∧ p3) → (False → True))) → (p5 ∨ False))) ∨ (p5 → ((p2 → (False ∧ p5)) → p5))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694177080098651215676841452669 : (((((((p4 ∧ p1) ∧ (p3 ∧ True)) → p5) → (False ∨ (p3 → (p3 ∧ False)))) ∨ (p5 → (((p5 ∨ (p5 → p1)) ∨ p5) ∨ (False ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172622994940920726219584983115 : (((p1 ∧ p2) ∧ ((p1 → (p1 ∧ p3)) → ((p4 ∧ (p2 ∧ (False ∨ True))) ∨ True))) ∨ (((True ∧ p1) ∧ (p1 ∧ ((p5 ∧ p2) ∧ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157259107448110340753601199642 : ((((((p4 ∨ p4) ∧ p3) → p3) ∨ ((p1 → p5) ∨ ((((p3 ∧ False) ∨ p4) → True) ∨ True))) → p1) ∨ ((p4 ∧ p3) → ((True ∧ False) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197147330356287483043429474329 : (((p1 → (((p5 → p3) ∨ p2) → p4)) ∨ p3) ∨ ((((p1 ∨ p1) ∨ (p3 → p1)) ∧ (p1 ∧ (((p3 ∧ (p1 ∧ p3)) → p1) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780490880911632632657478423126 : (((p2 ∨ (((p3 → ((((p1 ∧ p1) ∧ (p4 ∨ p5)) ∨ True) ∧ p5)) ∧ (p4 → p5)) → ((p4 → False) ∧ (p1 → ((p2 ∧ p5) → p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691377688673222339786109466130 : (((((p1 → (p2 ∨ p4)) → ((((p3 ∧ p1) ∧ p1) ∨ (p5 → (False → p5))) ∧ False)) → (p2 → (((True → (p2 ∨ p4)) → False) ∨ p2))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_624759232778436495771990600747 : ((((p5 ∨ (((True ∨ False) → (p1 → ((p4 ∧ p1) ∨ ((p4 ∧ (True ∨ ((p3 ∨ (p1 ∨ (p1 ∨ p1))) → p3))) → p2)))) ∧ p4)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340856498655368977606867443566 : (p2 → ((((False ∨ p5) → (((p3 ∨ ((p2 ∨ ((p2 → p1) ∧ False)) → p2)) ∨ p2) → ((p4 ∨ True) ∧ True))) → (False ∧ (p1 ∧ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468069986565661504983245267008 : ((((p4 ∧ ((p1 ∨ ((p5 ∧ ((False ∨ False) → p2)) ∨ (p1 → False))) → p3)) ∨ (((True ∨ False) ∨ ((p2 ∧ (p5 ∧ p1)) → p5)) ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622647895725923176028056933453 : ((((p4 ∧ ((p4 ∨ ((((p5 → (False ∨ p2)) ∨ False) ∧ (False ∨ p2)) ∨ ((p2 ∧ (True ∨ True)) ∧ p1))) → ((p3 ∨ p2) ∨ p4))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134656414816005331829148750061 : (((((True ∧ (p1 ∨ (p3 ∧ (p1 → p3)))) ∨ (True ∨ p5)) ∧ (((p2 → p4) → (p4 → p5)) ∧ (p3 ∧ p3))) → False) ∨ ((p5 ∧ p2) → p5)) := by
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
theorem thm_5_vars_124778135899382687214821640280 : (((p2 ∨ ((False → p4) → p1)) ∧ (p4 ∧ (p1 ∧ (True → (True ∧ ((False → False) ∧ ((True → p3) ∧ ((p1 ∨ p4) → p1)))))))) → (p4 ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700260714577148846194268751598 : ((((True ∧ ((False → ((p3 ∧ (p5 → p2)) ∨ (p2 → p5))) ∧ True)) → (((False ∨ p4) → (p1 ∨ (False ∨ p3))) ∧ (p2 ∧ (p1 ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624109464155340254812093119257 : ((((p2 ∨ ((p2 ∨ p4) → (((((p3 ∨ p1) → (p2 → p4)) ∧ (p2 ∨ p3)) → (((p5 → p3) ∨ p2) ∧ (p3 → p4))) ∧ p1))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_114058856288239121268374849118 : (((((True → (((p2 ∧ p1) ∨ p2) → ((p3 ∨ False) ∧ p3))) ∨ p2) → ((p1 ∨ p2) ∨ (p1 ∨ p4))) ∨ (True ∨ (True ∨ p1))) ∨ (p4 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875467676902806801966714608536 : ((((((((p4 ∧ p4) → p5) → (((((p1 → p2) ∧ (p5 ∧ False)) → (p3 ∨ p4)) ∧ (False ∨ p3)) → False)) ∨ p3) → p2) ∧ (False ∨ p3)) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((((p4 ∧ p4) → p5) → (((((p1 → p2) ∧ (p5 ∧ False)) → (p3 ∨ p4)) ∧ (False ∨ p3)) → False)) ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356245463277159057180090482526 : (p5 → ((((((False ∧ p5) ∧ p1) ∨ (((p5 → p5) ∨ p1) ∧ (p4 ∨ p1))) ∧ p4) ∧ p1) ∨ (((((True → p3) → p1) ∨ True) → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((True → p3) → p1) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56454578464386417477616298194 : ((((p1 → p4) ∨ (p5 → True)) → (((p1 ∧ p5) ∨ (((p1 ∧ p2) ∧ ((p2 ∧ (p3 ∨ p4)) → (False ∨ (False → p3)))) ∨ p3)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152513186611478630521314204902 : (((False ∨ (p4 → p3)) ∨ (((p3 ∨ ((((p3 ∧ (p2 ∧ True)) ∧ True) ∧ False) ∨ p2)) → (p4 ∨ p4)) → p3)) → (p3 ∨ ((False ∧ p4) → False))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39738793715879689857192833458 : (((p5 ∨ (p5 ∧ (p5 → ((True ∧ p4) → (((False → False) ∧ False) ∨ ((p3 ∧ (p4 ∧ ((True ∨ (p3 ∨ False)) ∨ p3))) ∨ p5)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169460106473759555095420374519 : (((((p2 ∧ p2) ∨ (p5 ∨ (False ∨ False))) ∨ (((True ∨ True) ∨ p5) ∨ False)) ∨ False) ∧ (((True → (p4 → (True ∨ p5))) → p1) ∨ (p3 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656340854845021260478922360695 : (((((((p2 ∨ (((p4 → p2) ∧ True) ∨ (p4 → p1))) ∧ True) ∧ p3) → ((p5 → p2) ∨ (True ∨ ((p1 ∨ p2) → p1)))) ∨ (False → p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_352033361492015840916885084526 : (p4 → ((((p4 ∧ (p1 ∧ p1)) ∧ p1) → (p3 ∨ p4)) → (((p5 ∨ (p2 ∨ ((p4 → (p3 ∧ ((p3 ∧ p1) ∧ p3))) ∧ p2))) ∧ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209153011602827340852698345772 : ((p3 ∨ ((p1 → p4) ∨ (p5 ∨ True))) → ((((((False → (p5 → (p3 ∨ True))) → True) → (p3 → (False → p4))) ∨ (p1 → p2)) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((((False → (p5 → (p3 ∨ True))) → True) → (p3 → (False → p4))) ∨ (p1 → p2)) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h4
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((((False → (p5 → (p3 ∨ True))) → True) → (p3 → (False → p4))) ∨ (p1 → p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h15 := h2 h11
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h19 : ((((False → (p5 → (p3 ∨ True))) → True) → (p3 → (False → p4))) ∨ (p1 → p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h19
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653582900203105819513185805417 : ((((((((False ∨ p2) ∨ ((p4 ∨ ((False ∨ p1) → p1)) → (p4 ∧ (p1 → False)))) → (p4 ∧ (p1 ∨ p1))) ∧ p4) ∧ p5) ∨ (True ∨ p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_183900575955206219603542510385 : ((((p4 ∨ p1) ∨ ((p1 → (p1 → (p2 ∨ p2))) → p4)) ∧ p4) ∨ ((p5 ∨ (p1 → ((((p5 → p2) → p1) ∧ (p5 → p4)) ∧ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157142800248198410547721905775 : ((((((((p4 → p2) → ((p3 ∧ p3) ∨ (p1 → p2))) ∨ (p1 ∨ p3)) ∨ p4) ∨ p3) ∨ p5) → p1) ∨ (((p2 ∨ True) ∨ p2) ∨ (True → p3))) := by
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
theorem thm_5_vars_179167001928341299221551887747 : ((p2 ∧ (p1 ∧ ((((False ∧ p1) ∨ p3) ∧ (True → (p1 ∨ p2))) → p1))) ∨ (((((p5 ∨ False) ∧ (False → p3)) ∨ False) ∨ True) ∧ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56766440095363274617435369163 : ((((True ∧ False) → False) ∧ ((p5 → (((True ∨ p1) ∨ ((p1 ∨ p3) ∧ (p4 ∨ p4))) → False)) ∧ ((p4 ∨ p1) ∨ ((p1 → p3) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159208165341722113276491609573 : ((p2 → ((p5 ∧ (p2 → ((False ∧ p2) ∧ p5))) ∧ (((False ∨ p4) ∧ (False ∧ (p4 → p5))) ∧ p4))) ∨ ((p4 ∨ (p1 ∨ (p1 → p1))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226659981771210483926970501162 : (((True ∧ p5) → p1) ∨ (p4 → ((((p1 ∧ p3) → (p3 → p1)) → ((p1 ∨ (((p2 → (p4 ∧ (True ∧ False))) ∨ True) ∨ p1)) ∧ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164742372795678489919749481936 : ((((((p1 ∨ p5) ∧ (p5 → (p1 → (False ∧ (p2 → p4))))) ∨ p2) ∨ (p4 → p5)) ∨ False) ∨ (False → ((((p4 ∧ p1) → False) ∨ p4) ∧ p4))) := by
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
theorem thm_5_vars_719873188350096902201990074417 : ((((p4 → ((p1 → p1) ∧ p5)) ∨ ((((p4 ∨ (p1 ∨ (p5 → p4))) → (p1 ∧ (p5 ∨ False))) ∨ (True ∨ (p4 → p5))) ∧ (p4 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_951424191899857741821119974974 : ((((p5 ∨ (True ∨ p2)) ∧ (True → ((((((p1 ∧ p4) ∨ p1) ∧ True) ∨ (((p4 → True) ∧ (p2 → True)) ∨ p2)) ∧ (p5 ∧ p4)) ∧ False))) → p4) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318656767036938540718998020062 : (p4 ∨ ((p4 → (((p4 ∨ (True ∧ (p2 → (False ∨ p4)))) ∧ ((p3 → (((p2 → p1) ∧ p3) → (p1 → p2))) → p5)) ∨ p1)) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325661904913626198197443084980 : (p5 ∨ (False ∨ (p1 → (((p5 ∧ (p2 ∨ (p1 → (False ∨ (False → (False ∧ p4)))))) → p2) → ((p5 ∨ ((p3 ∨ p2) → p3)) ∨ (p3 → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340483381859940918697949492253 : (p2 → ((((True ∧ (p2 → (p4 ∨ False))) ∨ (p3 ∧ (False ∨ True))) → (p1 → ((((p3 ∨ p3) → (p4 ∧ (p1 → p2))) → False) ∨ True))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228641058630665801958287727991 : ((p2 ∨ (False ∧ p4)) ∨ (((((((p5 ∨ p1) ∨ p5) → p4) → False) ∨ p3) ∧ ((False ∨ (p2 ∨ True)) → (((True ∨ p2) → True) → p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690237003164674035015225320138 : ((((p5 ∨ (p2 ∧ (p4 ∧ ((p5 → (False → (p4 ∧ p2))) ∧ (p4 → (p5 ∨ p1)))))) ∨ (((False ∨ (True → p4)) ∨ (p1 → p5)) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_777231559687718836919146935188 : (((p1 ∨ (((p2 ∧ (True ∧ (p1 ∧ p1))) ∨ ((((p4 → ((p2 → p2) ∨ p5)) ∧ p5) ∧ p4) ∨ (p1 ∨ p4))) ∨ ((p3 ∧ p5) → p3))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700068157649536429388302451525 : ((((((True ∨ False) → p2) ∨ ((p3 → False) ∨ (False ∧ (p5 ∨ True)))) → (p5 ∧ (p3 ∨ ((p2 ∨ (p3 ∨ ((True ∨ p1) ∧ p3))) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224375749207613927624475758775 : ((False → (p5 → False)) ∧ ((p5 ∧ (((p5 → ((True → p5) → (p5 ∧ (p3 ∨ False)))) → (p4 ∨ p3)) ∧ p2)) ∨ (((p1 ∧ p4) → True) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779542661247390006109508918602 : (((p2 ∨ (((p5 ∧ p4) ∨ (((((p2 → False) ∧ (False ∨ False)) → ((((p2 ∨ p5) → False) → p1) ∧ p2)) → (p2 ∨ p2)) ∨ True)) ∨ p2)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147602700870372889780364163980 : (((((p3 ∨ (((True ∨ p3) ∨ p1) ∧ True)) → ((False ∨ (p5 ∧ (p2 → p5))) → (p1 → p3))) ∨ False) → p1) ∨ (False → ((True ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718139254626250734299238925891 : (((((p1 ∧ (p3 ∧ False)) ∨ p1) ∨ (p4 ∨ (False ∧ ((p1 ∧ (((p3 ∨ (p5 → False)) → (((p2 ∧ False) → p5) ∨ p5)) → p1)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37707883301304361627233657339 : (((((p4 ∨ ((((((True → ((p2 → (p1 ∨ p2)) → p4)) → p4) → p1) ∧ p4) ∧ p5) ∧ p1)) → ((p2 → p3) → p4)) → p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480497847036885772617018995198 : (((((p4 ∨ (((True ∧ False) ∧ p4) ∧ True)) ∨ p5) ∨ (((True → p5) ∧ ((p5 ∨ (p4 ∨ (p2 ∨ ((p4 → p1) ∨ p4)))) → False)) → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p5 ∨ (p4 ∨ (p2 ∨ ((p4 → p1) ∨ p4)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63972717581113978051062630913 : ((False ∨ ((((((((p2 → p4) ∨ (p3 ∨ False)) ∧ (p1 ∧ p1)) → p2) → (((p1 ∨ p2) ∧ p5) ∨ p1)) ∧ p2) → (True ∧ p3)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655005023457243299889784803858 : ((((((p5 ∧ p3) ∨ ((p5 ∨ p5) ∧ (((p3 ∨ (p5 → p1)) ∨ p5) ∧ (p1 → ((True ∨ (p4 ∨ True)) ∧ p3))))) → p2) ∨ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174087537161767792547828386224 : ((((p1 ∧ ((True ∨ True) → (p1 ∧ (True ∧ True)))) ∨ (p2 → p2)) ∧ (p3 ∨ p4)) → (((p5 → (False ∧ p1)) ∨ p3) ∨ ((False ∨ True) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186860546689429229942315948512 : (((((p5 ∧ p2) ∨ True) ∧ True) → ((False → (True → p4)) ∧ p3)) → ((p1 ∧ ((p4 → (True → (False ∧ p1))) → (p5 ∨ p3))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160975349111103697948299884614 : (((p4 ∨ (p4 ∧ p3)) ∧ ((False → (p1 ∧ ((p4 → ((p2 → p5) ∨ p3)) → p4))) ∧ (False ∨ p5))) → ((((p5 → True) ∧ p5) → False) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317750331231259570842766158317 : (p4 ∨ (((((p5 ∨ p4) → p3) → (p3 ∨ ((((p5 → p5) → (p2 ∧ (p1 ∧ p4))) ∧ True) → p3))) ∨ ((p2 → p5) → (p3 ∧ p2))) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : (p5 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203632366146572779226349273744 : ((p2 ∨ (p3 → (p3 ∨ (p4 ∧ p3)))) ∧ ((((False → p5) → (False ∧ p1)) ∨ True) ∨ (False ∨ ((False → ((p3 → False) ∨ False)) ∨ (p5 ∧ p1))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245647855313861167822651675485 : ((p3 ∧ p1) ∨ ((((p5 ∧ (False ∧ p3)) ∨ True) ∨ ((p3 ∨ (p3 → (((False → p3) ∧ p5) ∧ ((False ∧ True) ∨ (p2 → p2))))) ∨ False)) ∨ p1)) := by
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
theorem thm_5_vars_167291457030245845447208958293 : ((((p4 ∨ ((p2 ∨ (((((p4 ∧ p5) ∧ p2) ∨ p1) ∧ True) → p5)) ∨ True)) ∨ p4) → False) → (p2 ∧ (False ∧ ((p2 ∧ (p3 ∧ False)) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((p2 ∨ (((((p4 ∧ p5) ∧ p2) ∨ p1) ∧ True) → p5)) ∨ True)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ ((p2 ∨ (((((p4 ∧ p5) ∧ p2) ∨ p1) ∧ True) → p5)) ∨ True)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342897318073862455977195035972 : (p2 → (((True ∨ (p5 ∨ True)) ∨ (p1 ∨ p1)) → ((p4 ∨ p5) ∨ ((p1 ∧ (((True ∧ (False ∧ p4)) ∨ p4) → ((False ∨ p1) → False))) → p1)))) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164592113624241868407557339911 : ((((True → False) ∨ (p1 ∧ (((True ∨ p3) → ((p3 ∨ p1) → True)) → (True ∧ p1)))) ∧ p3) ∨ (p3 ∨ (((True ∨ p2) → (False ∧ p1)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178776443893138997487349019875 : (((False ∨ (False ∧ True)) ∧ (p5 ∨ ((False ∧ (p1 ∨ (p5 → p1))) ∧ True))) ∨ (((p1 ∨ (p3 → (p3 ∧ (p2 ∨ p5)))) ∧ (False → p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48944981888080694616051990712 : (((((p5 ∧ p1) ∨ (((p3 ∨ p4) → (p3 → ((True ∧ (p1 ∨ True)) ∧ p5))) ∧ (p3 ∧ (p5 → p4)))) ∧ p2) ∨ (p1 → (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50785270532043327126240149119 : (((p4 ∨ ((((p2 ∧ False) ∨ False) → p1) → (True → ((True ∧ p3) ∧ (p4 → (p1 ∨ (p5 ∧ p5))))))) → ((p4 → p3) → (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117180673989438155184668070386 : ((True ∧ ((((False ∨ p5) ∨ (p5 ∨ (((p4 ∧ ((p3 → p2) ∨ True)) ∨ p1) → p2))) ∧ (p2 ∧ (False ∨ p2))) ∨ (p2 → p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165818239196444597481686591890 : (((p4 ∧ (p3 ∨ p3)) ∧ ((p5 → (p3 ∨ (((p5 ∨ p3) ∨ p1) ∧ p2))) ∨ (True ∨ p2))) ∨ (((False → (p4 ∨ p3)) ∧ p5) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731115208610779096123189550443 : ((((p1 ∨ (p5 → p4)) → (((p3 ∨ ((p5 ∨ (((False ∨ ((p3 → p2) ∧ p5)) ∧ (p3 → True)) ∧ (True ∨ False))) → False)) → p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152288872206074737083540324549 : ((((False → p4) → (p1 ∧ (True → p2))) → (p2 ∧ (False ∨ (((p2 ∨ (p1 ∧ p1)) ∨ False) ∧ (p1 → p1))))) → ((p4 → True) → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203018006184833880925950378250 : (((p3 ∧ p2) → (p2 → (False ∨ True))) ∧ ((((False ∨ p4) ∨ p2) ∨ p5) ∨ ((p4 → (((p5 → p2) ∨ p2) → True)) ∨ (p4 → (False → True))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620418257427545572187494930187 : (((((p5 ∨ False) ∨ ((((False → ((p2 → p2) → (p2 ∧ (p5 ∧ (p2 ∨ (p3 ∧ (p1 ∧ p4))))))) ∨ p4) ∨ p1) ∧ (p5 ∧ p3))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166527093016930045158064626818 : ((p4 ∨ (p1 ∧ ((((p3 ∧ (p2 ∧ p4)) ∨ (True ∨ p2)) ∨ ((p5 → p1) ∧ p3)) → False))) ∨ ((p3 ∧ ((p2 → (p5 ∧ p4)) ∧ False)) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341732870757627831847785138154 : (p2 → (((p1 ∧ p1) ∧ ((p3 ∨ p2) ∧ (((p3 ∨ p1) ∨ (((p1 → p4) ∧ False) → (p5 ∧ (p5 → p3)))) ∨ (True ∧ True)))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56441147378913778210940078721 : ((((p2 ∧ p5) ∨ (False ∨ p1)) → (((True ∨ p3) ∧ p1) ∨ (p5 → ((p4 ∨ (p1 → (p4 ∨ ((True ∨ p1) → (p3 → p4))))) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691887691875511029338265013174 : ((((p1 → ((((p2 ∨ p2) ∨ p2) ∧ (True ∨ False)) ∧ (((p3 ∧ p2) ∨ True) ∨ p2))) → ((p4 ∧ ((p5 → p4) ∨ (False → p5))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599075344763519731466397770634 : (((((True → False) ∧ (p1 ∧ (((False ∨ (p4 → p1)) ∨ (False ∧ ((True ∨ False) ∨ (p1 ∧ (((p1 ∧ p4) → p1) ∧ p4))))) → p4))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41188104715305300052140062180 : (((((((p4 ∨ (True ∨ p1)) ∨ (True ∧ True)) ∧ p3) ∧ (True ∨ (p4 ∨ (p2 ∨ ((False → p5) → False))))) → (p4 ∨ (p4 ∧ False))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126082035634254046750832495841 : ((True ∧ (((((((((p4 ∨ False) ∨ p5) ∨ p1) ∨ (p5 ∨ False)) ∨ p1) → False) ∧ (((p5 ∨ False) ∨ p5) ∨ p5)) ∧ p1) ∨ False)) → (p5 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h26 : (((((p4 ∨ False) ∨ p5) ∨ p1) ∨ (p5 ∨ False)) ∨ p1) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h27 := h21 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h30 : (((((p4 ∨ False) ∨ p5) ∨ p1) ∨ (p5 ∨ False)) ∨ p1) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h31 := h21 h30
        -- False on the left can always be used.
        apply False.elim h31
    case inr h32 =>
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h33 : (((((p4 ∨ False) ∨ p5) ∨ p1) ∨ (p5 ∨ False)) ∨ p1) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h34 := h21 h33
      -- False on the left can always be used.
      apply False.elim h34
  case inr h35 =>
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762512775919064267295781368205 : (((p3 ∧ ((((p3 → p4) ∧ ((p5 ∨ p1) ∧ ((((p3 → p5) ∧ p5) ∨ False) ∧ False))) ∨ p2) ∧ (((p5 ∧ p3) ∧ (p5 ∨ p4)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601374547175033369844486015790 : ((((p2 ∧ (p4 ∧ (((p1 ∧ p4) ∧ p1) ∧ (((p5 → (p2 → p3)) → p3) ∧ ((((p5 ∧ p4) ∧ p2) ∧ True) ∨ (p3 ∧ p5)))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313106251506960256151471004508 : (p3 ∨ (((p3 ∧ ((p1 → p4) ∨ ((((True → ((p2 ∧ p3) → p1)) ∧ (p4 ∧ p5)) ∧ (p1 ∨ p1)) ∨ p5))) ∧ (p3 ∧ (p1 ∨ p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808049862687998182305015924724 : (((p4 → (True ∧ (p3 → ((((p1 → ((p2 → (p4 ∨ (p4 ∧ ((False ∨ p3) ∨ (p4 → p5))))) ∧ False)) → p2) ∨ p3) → (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85286972166881385291694056093 : (((((True ∨ (p5 ∨ ((p4 ∨ (p1 ∨ p1)) ∧ p4))) → p1) ∧ p4) ∧ (p4 → (((p5 ∨ (p4 ∧ (p1 → True))) ∧ (p2 ∧ False)) ∧ p5))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193270786746952276162833068337 : (((p4 → (p2 ∧ p1)) ∧ ((p2 ∧ p2) ∧ (p2 ∨ p2))) → ((p5 ∨ p2) ∧ ((p5 ∨ ((p2 → (True → ((p5 ∨ p5) → p4))) ∧ p4)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h11.left
  let h13 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671531367210298055411382986533 : ((((p4 → ((p5 ∨ (((True ∨ (p5 ∧ p5)) ∨ (p5 → ((p1 ∧ (p2 ∨ p3)) ∨ (True ∧ p2)))) ∧ p1)) ∧ p4)) ∨ ((p2 ∧ p2) → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_208497571951962212179513067444 : (((p1 ∧ False) → ((True → p5) ∨ p1)) → ((p3 → (((p5 ∧ False) ∧ p1) → (False ∧ p3))) ∧ ((p5 → ((p5 → (p5 → p5)) ∧ p4)) ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



