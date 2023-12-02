variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148579651118202259217171342484 : (((((p5 → (False ∧ (False ∧ p5))) ∨ (p3 ∨ False)) ∨ False) ∨ (((False → (False ∨ p2)) ∨ p4) → (p1 → p3))) ∨ ((False → True) ∨ (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149494429564862470151254992285 : ((p1 ∧ ((((p5 ∧ (p4 → (p5 → (p4 → False)))) → (p3 ∨ (True ∧ ((p1 ∧ p2) → False)))) ∨ p2) → p3)) ∨ ((False ∧ (True ∧ True)) → p1)) := by
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
theorem thm_5_vars_991581756426802152649503009019 : (((p4 ∧ (((p5 ∨ ((((p1 ∧ p1) → p1) → p2) ∨ (False → (False ∨ (p3 → ((p2 ∧ p5) ∧ False)))))) ∧ (p4 → False)) ∧ (p3 → p5))) → p5) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h15 := h7 h14
      -- False on the left can always be used.
      apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623656047138451609622740731086 : ((((p1 ∨ (((p2 → p1) ∧ (((((True ∧ (p2 ∨ p3)) ∧ (p3 ∨ p3)) ∨ ((True ∨ (p1 → p5)) → p4)) → p1) ∧ p4)) ∧ True)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134374140482874695414659421101 : (((p3 ∨ ((((((True → p2) → (p5 ∧ p3)) ∨ p1) → ((p4 ∧ ((p1 ∨ p4) ∨ True)) → p3)) ∨ True) ∨ p5)) ∨ p2) ∨ (False ∨ (p5 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698879991946731596412560455026 : ((((p1 ∧ ((p3 → False) ∧ (((p3 ∨ (p1 ∨ p1)) ∨ p1) ∧ False))) ∨ ((False → True) ∨ ((False → p4) ∨ (False → (p1 ∨ (True ∨ p2)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149083519202230283655284888291 : ((((p4 → p4) → True) → (p1 ∨ (((p4 → p4) ∨ ((p5 → ((p1 ∨ p5) ∧ p1)) ∧ (p2 ∧ p4))) ∧ p4))) ∨ (((p3 ∧ p4) ∧ True) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149807119298995992621080981674 : ((False ∨ (p5 ∨ ((((p3 → (p3 ∧ (p5 ∧ (p5 ∧ p2)))) ∨ p2) ∨ p3) ∨ ((p1 ∨ p1) ∨ (True ∨ p3))))) ∨ (((p1 ∧ p3) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215393502464904242542628497871 : ((p2 ∧ (True ∨ (p3 ∧ p5))) ∨ (((p1 → (((((((p1 → False) ∧ p3) → (False ∧ p3)) ∧ p1) → False) ∧ p3) → p5)) → False) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607295281118767422559543524513 : (((((((p1 ∨ False) ∧ p5) ∨ (False ∧ (((((p5 → p5) → (False ∧ p2)) → True) ∧ p5) → ((False → (p1 ∧ True)) ∧ p4)))) ∧ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42381460532893672770005406059 : (((p4 ∧ (((p5 ∧ True) → (((True → (p1 → p3)) ∨ (True → ((p5 ∧ (p4 ∨ False)) ∧ False))) → (True ∧ False))) → (p5 ∨ p3))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204339265190352538046728615989 : (((p5 ∧ (p5 ∧ (p5 ∨ p3))) ∧ p4) ∨ ((((False ∧ ((p2 → False) → (p3 ∧ p3))) → ((p2 → (False ∨ p4)) ∧ p4)) ∧ p1) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185261850497356464131141367246 : ((p1 ∧ ((False ∨ (p3 → p4)) ∨ (((p2 → p3) ∨ p3) ∧ p1))) ∨ ((False → ((((True → True) → False) → (True ∧ (p1 ∨ p3))) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112005347442018549437009253682 : ((((p3 → ((False ∨ p1) → False)) ∨ ((((p4 → (p4 → True)) ∧ (p5 ∧ False)) ∧ (p2 ∨ ((p2 → p4) ∧ p1))) ∨ True)) ∨ p5) ∨ (p4 → p1)) := by
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
theorem thm_5_vars_179735763137199774739006360050 : ((((((True ∧ p5) ∨ (p4 ∧ (False ∨ True))) ∧ p5) ∧ (p1 → p3)) ∧ p3) → (((((True → p2) ∧ False) ∧ ((p4 ∧ False) → False)) ∨ p5) ∨ False)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58843403767218957241644519645 : (((True ∧ p1) ∨ (p2 → ((p5 → ((False → p3) ∨ True)) ∧ ((((p1 → p1) → ((False → (p1 ∨ p4)) ∧ False)) ∧ (p4 ∧ p5)) → False)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p1 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727477664688654573978722643849 : ((((p3 ∧ (p2 → p3)) ∨ (((((True ∨ p1) → False) ∨ p2) ∨ ((((True ∧ (p4 ∧ (p1 ∨ p1))) → p1) → (True ∨ p1)) ∧ p4)) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_304677998667702924184216120825 : (p1 ∨ ((((((p5 ∧ ((True → False) ∧ p1)) → p4) → p4) ∧ (p2 ∨ ((((p3 ∨ True) ∧ p4) ∧ (p3 ∨ p5)) ∧ p5))) ∧ True) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44912450940040123370721763574 : ((((p3 → (False ∨ p3)) → ((False ∨ ((True ∧ True) → ((p2 → p3) ∧ (False ∨ ((p4 ∧ p2) ∨ (p5 ∨ p2)))))) → (p5 → p4))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169079136804190825787624893750 : ((p3 → (True ∨ (p4 ∨ (False → ((True → p5) → ((p3 ∧ (True ∨ (p2 ∧ True))) ∧ False)))))) → (((p1 ∧ p5) ∨ p5) ∨ (True ∨ (p2 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343426978460632721793799712995 : (p2 → ((p1 ∨ False) ∨ (True ∧ (((((p2 ∧ True) → ((p3 ∨ True) → (((False → p2) ∧ p3) ∧ p4))) → p1) ∨ True) ∨ ((p5 ∨ p1) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_722234009476052179851940317451 : ((((p5 → (p3 ∨ (True ∨ False))) → (((p5 ∨ p4) → (((p2 ∧ (p2 ∨ (p3 ∧ False))) ∨ ((p1 ∧ p3) ∨ (False ∧ p1))) ∨ p5)) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713497777743214106326310932809 : ((((p4 → ((p1 ∨ False) ∨ (p5 ∧ p3))) ∨ (((False ∧ (False ∨ p1)) ∧ (((False → p1) → p1) ∧ ((p4 → (p4 ∧ p5)) → p3))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65870728572610569271088357800 : ((p4 ∨ ((False ∨ p2) ∨ ((p3 ∧ (p1 ∧ (p5 ∧ p4))) ∨ (p5 → (((p1 ∨ (((p3 → p5) ∧ (p3 ∧ p1)) → True)) ∧ p3) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167417081029710521024158907712 : (((p1 ∧ ((p3 → (((p1 → ((False → p5) ∨ p4)) → (p4 → False)) ∧ False)) ∨ p5)) → False) → (((p4 → ((p1 → p5) → p5)) ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47061573473050200435193949653 : ((((((((p3 ∨ ((True ∧ p3) → False)) ∨ p5) ∧ p4) → ((p2 ∧ False) ∧ p4)) ∨ ((p4 → False) → True)) ∨ (True ∧ p1)) ∨ (True ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780177561400659722955572872696 : (((p2 ∨ ((p4 ∨ ((((p5 ∧ p5) → (p2 ∨ p5)) → p3) ∧ (p4 ∧ ((p1 ∧ p2) ∨ ((True → p5) → p5))))) ∧ (p4 ∨ (p4 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213561511819663146143227183836 : ((((False ∨ p2) ∧ True) ∨ False) ∨ ((((True → p4) ∧ p5) ∧ ((False → p5) → ((((p1 ∧ p1) → p3) → (p1 → p2)) ∨ p5))) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49817585695058263535385865100 : (((p2 → ((((((p5 ∨ p2) → (p1 ∨ (p3 → p2))) ∨ (p5 → p2)) ∨ p1) → (p5 ∧ (p4 ∧ True))) ∨ p2)) → (False ∧ (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151589053496401765247148971756 : (((((p5 → p5) ∨ ((True → False) ∧ p3)) ∨ ((p4 ∨ (p5 → (p2 ∧ (p2 ∧ p1)))) ∧ p3)) → (p5 → p5)) → ((p2 → (True ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675412795696925348988554745480 : ((((((p5 ∧ (p5 ∨ (False ∧ p3))) ∨ (((p3 ∧ (True ∧ (True → p3))) ∧ True) → (p2 ∨ p4))) → p3) ∧ (p1 ∧ (p4 ∧ (p3 ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147553674359477920396262063388 : (((p5 → (True ∧ ((p2 ∨ ((True → (p1 ∨ (((p3 → False) ∨ p3) ∧ (p4 → p2)))) ∨ p1)) ∨ True))) ∨ p5) ∨ ((p5 ∧ (False ∧ True)) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_60613935502343694377525717911 : ((True ∧ (((((False → (True ∨ True)) ∧ p1) → (((p2 ∧ (True → False)) ∨ True) ∧ p3)) → ((p1 ∨ (p1 ∨ p4)) → p1)) ∨ (True ∨ p3))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_702651335095658244601413176817 : (((((((True ∧ (p3 ∨ True)) ∨ p1) → p4) ∧ (False → p5)) ∨ (True ∧ (((p4 → p1) → p1) → (((p3 ∧ (p4 → p2)) ∧ False) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42234085722792579548520894528 : (((False ∧ ((p2 ∨ (p3 ∨ p1)) ∧ (p1 → ((((p1 → (p4 ∨ p3)) → ((p2 ∧ p2) ∨ p3)) → (False → (False ∨ p5))) → p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137205653713120046511124034044 : ((False ∧ (p4 ∨ (((p3 ∨ p1) ∨ p3) ∨ ((p5 ∧ p5) → (((p2 ∨ ((False ∧ p2) → (p5 ∧ p2))) ∨ p2) → p4))))) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54077979862600142172627107626 : ((((p1 ∨ False) ∧ (((True → False) ∨ p1) ∧ (True ∨ p1))) → (((True → ((p3 → p3) ∧ p4)) → ((p4 → (True ∧ p3)) → p5)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
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
theorem thm_5_vars_357263823916340698413497049358 : (p5 → ((p2 ∧ p2) ∨ (((((p2 ∨ (False ∧ p2)) ∨ p3) ∧ p3) ∨ p5) ∨ (False ∨ (True ∨ ((p2 ∨ (p3 ∨ (True → (p3 ∨ True)))) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317880974555704606131130054398 : (p4 ∨ ((True ∧ (((((p5 → (p5 → (p5 → True))) → (False ∧ True)) → (p4 ∧ (p3 ∨ ((p4 ∨ (p5 ∧ p1)) → True)))) → p1) ∨ True)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111505832006470701330458073463 : (((p4 → ((((p2 ∨ p4) ∨ (p3 ∧ (p5 ∧ (p3 ∧ p3)))) ∨ p2) → (p2 ∨ ((p3 ∨ (p2 ∧ False)) ∧ (p1 ∧ False))))) ∧ True) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46789764504107202805492145216 : (((p5 → ((p3 → (((True → (((p3 ∧ False) ∧ p1) → p5)) → (False ∧ p3)) ∧ ((p2 ∧ True) ∨ (p2 → p4)))) ∧ p4)) ∧ (p5 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119527036474962651142234962060 : ((p5 → ((p5 → (p4 ∧ ((p2 ∨ p5) ∧ ((True ∨ p1) → ((p1 ∧ p3) ∨ (((True ∨ p3) → (p2 ∨ p5)) ∧ p3)))))) ∨ p5)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247601262378649488656159331967 : ((False ∨ p5) ∨ (((p1 ∧ ((p4 → p5) → (p5 ∧ ((False ∧ ((True ∧ p2) ∧ p3)) ∨ ((p4 ∨ True) → p2))))) ∧ (True ∧ p3)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65333661064870570780562269587 : ((p3 ∨ ((True ∧ ((p4 ∨ (p1 → True)) → (True ∧ (p5 → (p2 ∧ ((p4 ∧ p5) ∨ (True → p4))))))) ∨ (((p1 ∨ p2) ∨ p1) → True))) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672517889303816224084756756696 : (((((p2 → (p1 → ((((p4 ∧ p3) ∧ ((False ∧ p1) → p2)) ∨ p2) ∨ ((p4 ∧ p2) ∧ (p3 ∨ p4))))) → p4) → ((False ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124343773119347793689615235924 : ((((((True ∧ (p5 ∨ p3)) → p3) ∨ p5) ∧ p3) ∨ ((p3 ∧ (p1 → ((p2 ∧ (p4 ∧ (True ∨ False))) ∧ (False ∨ True)))) → True)) → (p2 → p2)) := by
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
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114885560305017878286005219094 : (((p1 ∧ ((p1 ∧ (p2 ∨ (p1 ∨ (True ∨ ((p5 ∧ False) ∨ p1))))) ∧ p1)) ∨ (((True ∧ False) ∧ (False ∧ (p4 ∨ False))) → p1)) ∨ (p1 ∨ p4)) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204136461245245775129143133120 : ((((p4 ∨ (p4 ∨ p5)) ∧ p2) ∧ p3) ∨ ((False → (True ∧ (p1 → (p1 ∨ (p2 ∧ (p3 → (p5 → False))))))) ∨ ((p3 ∨ (p1 → False)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114109248051971890031638733617 : (((False ∨ (((p2 ∨ (False ∧ ((p5 ∧ p2) ∨ (p3 ∨ False)))) → p3) ∧ (((False ∧ p2) → p2) → p2))) ∨ ((True ∧ False) → p1)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763403664693699917501365738616 : (((p3 ∧ (True ∧ ((False → p4) → (p1 → (p3 ∧ (((((p4 ∨ ((p1 → p4) → (p5 ∨ False))) → False) → (True ∨ p1)) ∨ True) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37386085265318949179241607323 : ((((((((p2 ∨ p4) ∧ p3) ∨ (p1 ∨ (p3 ∧ False))) ∨ ((p1 → (p1 ∧ ((p1 → p3) ∨ (p2 ∨ p5)))) → p4)) → p4) ∨ p1) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57011563119982417126227880938 : (((False → (p5 ∧ False)) ∧ (p2 ∨ ((False ∨ ((p3 → p5) → (((p5 ∧ p5) ∧ ((((p5 ∧ p5) → p2) → p5) → p4)) → False))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303816086644604623546557093378 : (p1 ∨ (((p1 ∨ ((p3 ∧ (p1 ∧ ((p3 ∧ p3) → ((p4 ∧ p4) ∧ (((p1 ∧ ((p3 → p2) ∧ True)) ∧ p4) ∨ p2))))) → p2)) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193704119917926092934945650031 : ((p1 ∧ (p2 → (((p5 → False) ∨ True) → (p2 → False)))) → (p3 → (((p4 ∧ p4) → ((False ∧ (True ∧ p4)) ∨ (False ∧ (True → p5)))) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608363385829944759549511753014 : ((((((p3 ∧ (((False ∧ ((False ∨ p3) ∧ True)) → (((False ∧ (True → p5)) → p5) ∨ ((p1 ∧ True) ∧ p2))) → p2)) ∨ True) ∨ False) ∨ p1) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213301403048229319908421223546 : (((True ∧ (p3 ∧ p1)) ∧ p5) ∨ ((((p5 ∨ (((p3 ∨ (p3 ∨ p2)) ∧ p5) ∧ False)) ∨ p2) ∨ (True ∨ (p4 → p3))) ∨ (p1 ∨ (True → p1)))) := by
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
theorem thm_5_vars_627175705647739731358176042966 : (((((((p3 → (((True ∨ (p1 → ((p3 ∨ p1) ∨ (p2 → p3)))) ∨ (p1 → ((p4 ∨ False) ∨ p1))) ∧ False)) → True) ∨ p3) ∧ p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668598351722918537014167522274 : (((((False ∧ ((p4 → ((p1 ∨ p4) ∧ (False ∧ ((p2 ∨ (p3 ∧ (p4 ∨ p1))) ∨ False)))) → (p4 ∧ p5))) ∧ p4) ∨ (p3 → (p3 ∧ p3))) ∨ False) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119319964066905179252183548677 : ((p3 → (((p3 ∧ (False → False)) → ((p5 ∨ (((p3 → p4) → p4) ∨ p5)) ∨ (p4 ∧ p4))) → ((p1 → p4) → (False ∧ p5)))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50377748885180009551519912567 : ((((p4 ∧ p4) ∧ ((((p2 ∧ ((p1 ∨ True) ∨ p4)) ∧ p1) ∨ False) → (True → (p5 ∧ (True ∨ p2))))) ∨ (p1 ∧ ((p3 ∧ p1) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61481468027810839712813503121 : ((p1 ∧ ((((p5 → ((p4 → p2) ∨ ((p2 → p4) → (p2 ∧ (p1 ∨ ((p4 → p4) ∨ p3)))))) ∨ p5) ∧ p5) ∧ ((True ∨ p4) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234653917094203132075022495429 : ((p4 → (True ∧ True)) → ((((((p4 ∧ p1) ∧ p5) → ((((p4 ∧ (True ∧ p2)) ∨ (p1 → p4)) ∨ False) ∧ p4)) ∧ p3) → False) ∨ (False → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300811710152217069334915752422 : (False ∨ (((((False ∨ (p1 → ((False ∧ (False → p3)) → p2))) → p5) ∧ False) ∨ (p3 → True)) → (((p4 ∧ ((p5 ∨ p5) ∧ p5)) → p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252640429420036503851479297460 : ((p5 → p4) ∨ ((((p5 ∧ (((p3 → False) → p3) ∨ p2)) ∨ ((p2 → (p5 ∨ True)) ∨ p2)) ∧ (((False ∧ True) → p5) ∨ False)) ∧ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197825981783619307719303300095 : (((p1 ∧ (False ∧ p3)) ∨ ((p1 ∧ p2) ∨ p4)) ∨ (False → ((((True ∨ p3) ∧ False) → (True → ((p4 → False) → p3))) → ((p5 ∧ p5) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110851888156654234834213882297 : ((((((((False ∨ p5) ∨ ((p5 → False) ∨ p4)) ∨ ((((p5 → True) ∨ p1) → (p4 ∧ p5)) → False)) → True) ∧ p3) → False) ∧ p2) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265017661742221122654119249560 : (True ∧ ((p5 → p3) → (p5 ∨ (((False ∨ (p3 → (True → (p5 → (p3 ∧ (p2 ∧ (p1 → p5))))))) ∨ (False ∧ (p3 ∨ (False ∧ p4)))) ∨ True)))) := by
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
theorem thm_5_vars_193200301028769333570973545477 : (((p1 ∧ (p4 ∨ (False ∨ p1))) → ((p4 ∧ p5) ∧ True)) → ((p5 ∧ p2) ∨ ((p4 → True) ∨ (p3 ∨ (p1 ∧ (p1 ∨ ((p3 ∧ p2) ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307243304984751061969320536195 : (p1 ∨ (p2 ∨ (((True ∧ p2) ∧ ((True ∨ (False ∨ (p1 ∧ p1))) → (p3 ∨ (p4 ∧ (((p4 ∧ (p3 ∨ p4)) ∧ (p5 ∨ p2)) ∧ p5))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42972109069684466908804938862 : (((p5 → ((True → ((((((p5 ∧ True) → (p3 ∧ (False ∧ True))) ∧ True) ∨ (p1 ∧ (p2 ∧ p2))) ∨ p4) → p1)) → (p3 ∧ p2))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135078055149955240893028365950 : (((((p2 ∨ (((((p4 ∨ (False → True)) → p5) → p2) ∧ False) ∨ p3)) ∨ p4) ∧ ((p2 ∨ True) → p3)) ∨ (False → p3)) ∨ ((False → True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622872521207685582467873216 : ((((p5 ∧ p5) ∧ ((p2 ∧ (p3 → ((p1 → False) ∨ ((p2 → p5) ∧ ((p1 ∨ p2) ∧ (p1 ∨ True)))))) → p5)) ∨ (p2 → p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190527014936869130891916707549 : ((((True ∧ ((True → False) ∨ (p2 ∧ p1))) → p1) → p1) ∨ (((((p1 ∨ (True → p3)) ∨ True) ∨ (True ∨ False)) ∨ (p1 ∧ (False ∧ p3))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115212554975375002191061897434 : (((p2 ∨ ((p4 ∧ True) ∨ ((p4 ∨ True) ∧ (p2 → False)))) ∧ ((True → ((((True → p2) ∧ False) → p3) ∨ (p5 → True))) → True)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680828324186873860356956332246 : (((((p3 ∧ (p4 → False)) ∨ (((p1 ∧ ((((True → p4) ∨ True) → p4) ∧ p3)) ∧ p1) → (p3 ∨ False))) → (((p5 ∨ p4) → p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50987814692479973968511794929 : ((((p2 ∧ p5) ∧ ((True ∧ (((p1 ∨ True) ∧ False) ∨ p5)) ∨ (p3 ∧ ((p2 ∨ p5) ∧ True)))) ∧ ((False → ((p5 ∨ p4) ∨ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165283414786725864112057460979 : (((((((p4 ∨ p4) ∨ (p3 ∧ p1)) → p1) ∧ p1) ∨ ((True ∨ p5) ∨ p5)) → (p5 ∧ p5)) ∨ ((False → ((p2 → p5) ∨ False)) ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41604967440849506674932643965 : ((((((p1 ∨ p2) ∧ p2) ∧ (p5 ∧ (False ∧ p5))) ∨ (p5 ∨ ((False ∧ ((p1 → (p3 ∧ True)) ∨ p5)) → ((p4 → True) ∧ False)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171339510105868856527030306926 : ((((((p2 → ((p5 ∨ p3) ∧ (p4 ∨ p2))) → (p5 ∧ p2)) → p4) → p3) ∧ p3) ∨ (False → (p5 → (False ∨ (((False ∧ p2) ∧ False) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109737624363193780676095565338 : ((p4 ∨ (p4 ∨ (((((p5 ∨ p1) ∨ ((p5 ∧ p5) ∧ p2)) ∧ p3) ∧ (p3 → ((p1 ∧ p4) → p3))) → ((False ∨ True) ∨ p1)))) ∧ (False → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190131155359311016949484296987 : ((((p1 ∧ p2) ∧ ((True ∨ p4) → (True ∨ True))) ∧ True) ∨ (((p3 → True) → ((p4 → p3) → ((p4 → (p3 ∧ (True → p4))) ∨ True))) ∨ p5)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42632657169944796244550240869 : (((p3 ∨ (True ∧ (p3 → ((p1 ∧ (p1 → (True ∧ (((((p1 → p4) ∨ p5) ∨ False) → True) → ((False ∨ p1) → False))))) ∧ False)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747628425245737739453429425137 : ((((True → p4) → (p1 → (((False ∧ (True ∨ p4)) ∧ (((p2 ∨ (p3 → p5)) → p2) ∨ (False → (False ∨ p3)))) ∨ ((p2 ∨ p3) → True)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187391002107599382261682924369 : ((p4 ∧ (((((p2 → p3) ∧ p1) ∧ True) → (True ∧ True)) → p2)) → ((False ∧ (((False ∨ (p4 ∧ (p1 ∧ p2))) ∨ p4) ∧ False)) ∨ (p1 ∨ True))) := by
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
theorem thm_5_vars_217673132234504493093437151095 : ((((True → p3) → p1) → True) → (p1 → (((p1 ∧ (True ∧ (p1 → (((p4 → True) → True) → p4)))) ∧ (p1 ∧ (False → p1))) ∨ (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589021822990240560178171352957 : (((((p1 → (((p2 ∧ (((p5 → (p1 → (p2 → (True ∨ (p2 → False))))) ∨ (p2 ∨ True)) → p5)) ∧ p3) ∨ (p4 ∧ p1))) ∨ True) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191574351933534360942557582610 : ((p2 ∧ ((p3 → (p1 ∨ ((False ∨ True) ∨ False))) → False)) ∨ (((False ∧ (p5 → p5)) → (((True ∧ True) ∧ (True → (p5 ∧ False))) → p3)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340637200458548779354031236417 : (p2 → ((p3 ∨ (p3 ∨ (((True → p3) ∧ (True ∧ ((((((p2 ∧ ((p4 ∧ p1) ∧ p3)) ∧ p2) ∨ p2) ∧ True) ∨ p5) → p1))) → p1))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (((((p2 ∧ ((p4 ∧ p1) ∧ p3)) ∧ p2) ∨ p2) ∧ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119187080653820073291799043214 : ((p2 → ((((True → (((p4 ∨ ((p3 ∨ True) ∧ p3)) ∧ True) ∨ p5)) ∨ (p4 ∧ (p3 → (True → p1)))) ∧ p4) ∨ (p3 ∧ p4))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612467979399448719684285264277 : ((((((((p1 ∨ True) → (p2 ∨ (False → False))) ∧ (((False ∧ p5) ∨ (p5 → True)) ∨ (p2 ∨ (True ∨ p1)))) ∧ p3) ∨ (True ∨ False)) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58395714868889593607720738829 : (((p2 ∨ True) ∧ ((((False ∨ ((p5 ∧ ((p1 → False) → True)) ∧ ((p3 ∨ ((p3 ∧ p4) ∧ True)) → p2))) → p1) → p2) → (True → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52334021613673603861084376027 : ((((((((False ∧ (p3 ∧ True)) ∨ (True ∧ p1)) → p1) → p3) ∨ p1) → False) ∧ (False ∨ ((False ∨ ((True → False) ∧ (p2 → p1))) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1966626542341085433917571604 : (((True → p2) ∧ ((p4 ∨ p1) ∧ (p4 ∨ (((p4 ∨ False) → (True → (False ∧ True))) ∨ (p3 ∨ p4))))) ∨ (True → ((False → p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137678469462955097832419089799 : ((p1 ∨ ((((p5 → ((p5 ∨ True) → False)) ∧ ((False ∧ (p4 ∨ True)) ∧ (p4 ∨ True))) ∨ ((False → False) ∧ True)) ∧ p4)) ∨ ((p1 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617246520602101587164184884744 : (((((p5 ∧ ((((p4 ∧ p4) ∧ p3) → p4) ∨ p5)) ∨ ((p1 → (True → (p2 ∨ p5))) ∨ ((p2 → True) → ((p4 → p2) ∨ True)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135037764660084376575894656388 : (((((False ∨ p5) ∨ (p2 ∧ ((((p4 → p3) → p3) ∧ p4) ∧ ((p5 → p1) → (p1 → p4))))) ∧ False) ∨ (p1 ∨ True)) ∨ ((p5 ∨ True) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263900937761683708410133455594 : (True ∧ ((False ∧ ((p5 ∧ (True → p4)) ∨ (p3 → ((p5 ∨ p2) ∧ (p5 → p2))))) ∨ ((p5 ∧ (((True ∧ p3) → (p3 ∧ True)) → p4)) → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ p3) → (p3 ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682773268028130665776007811599 : (((((p2 → ((False ∨ p1) → p3)) → ((False ∨ (p2 ∨ p5)) → ((p1 ∧ p4) ∨ (False ∨ True)))) ∧ (p4 → ((p3 ∨ p3) → (p3 → p3)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198629588917297965855815053539 : ((p3 ∨ ((p4 ∨ ((p4 ∧ p3) ∨ p5)) ∧ p4)) ∨ (p2 → (((True ∨ ((p2 ∨ (p5 ∧ p1)) ∨ ((False ∨ p3) → p1))) ∨ (p4 → p4)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58323701637104546218914327381 : (((False ∨ False) ∧ ((((False ∨ p3) ∧ p1) ∨ ((True ∧ p5) ∨ p1)) → ((((p4 → p2) ∧ (p4 ∨ True)) ∨ (p3 ∨ (p2 → p5))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



