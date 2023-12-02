variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116072684089996645002209022035 : ((((False → p2) ∧ p5) ∧ (p4 → (p1 ∧ (((True ∧ p4) ∨ p1) → ((False → p3) → (((p3 ∨ p3) → p1) ∧ (p4 ∨ p3))))))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192400402164341140023879653464 : (((((((p5 ∧ p4) ∧ p1) ∧ False) ∧ p1) ∨ p3) ∨ p5) → ((p4 ∨ True) ∧ (p5 → ((p2 → ((p1 ∨ p1) → p4)) ∨ (p5 ∧ (p5 ∨ p1)))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h26
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197528035273873663976832238586 : (((((p5 ∧ False) → True) ∧ p3) ∨ (False ∨ p2)) ∨ ((p2 ∨ p4) ∨ ((p1 ∨ (p5 → False)) ∨ (p4 ∨ (True ∨ ((p4 ∧ (p3 ∨ p4)) ∧ p2)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341693466747911069511341651804 : (p2 → (((((p3 ∧ ((True ∧ p1) → (p5 → p2))) ∧ (False ∧ ((((p5 → p5) ∧ True) ∧ False) ∨ p4))) ∨ p5) ∨ (p4 ∨ p2)) ∨ (False ∨ p4))) := by
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
theorem thm_5_vars_152355360173249379056534139967 : ((((False ∨ (p3 → p4)) → p2) ∨ (p5 → ((((False → False) → (True → p5)) → p1) ∨ ((False → p1) ∧ p3)))) → (p2 → ((True ∧ p2) ∧ p2))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234944240844876397701914711612 : ((True ∧ True) ∧ (p5 ∨ (((p4 ∧ (((p2 ∨ ((False → (False ∨ False)) → p1)) ∧ (True → ((p1 ∨ p1) ∧ p4))) ∨ p3)) ∨ (True ∧ True)) ∨ p3))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723747273808109167149375107832 : (((((p1 → p2) → False) ∧ ((p5 ∧ (((((((p3 → True) → True) → True) → (p1 ∧ p2)) → (False → (p3 → p3))) ∨ p2) → True)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200848605311690040484098626447 : ((True ∨ (((p5 → p5) ∨ False) → (p2 ∨ p4))) → ((p3 ∨ (((((False → p3) ∧ (((True ∧ p4) ∧ p1) → p1)) ∧ p3) ∨ p1) ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_160016131126235831720542796156 : ((((p1 → (p3 ∧ p3)) ∧ ((p3 ∨ ((p1 ∨ (p4 ∧ ((p4 ∧ True) ∨ p1))) ∧ p3)) ∧ True)) → True) → ((True → False) → ((p5 ∨ p5) ∧ True))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661625555868214543760221290160 : ((((((p3 → (True ∧ ((True ∧ (((p4 ∨ False) ∨ p5) → False)) → (p3 → (p5 ∧ p2))))) → p2) → ((p4 ∧ p1) ∧ p5)) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111639302031785377365019064771 : ((((((p5 ∨ p4) → (p3 ∨ ((p1 ∨ p1) ∧ False))) ∨ ((True → ((True ∨ p3) → p3)) ∨ (p5 ∨ (p1 → p2)))) ∨ p4) ∨ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614605384629905242831885542180 : (((((p3 ∧ ((((p2 ∨ p5) → p4) → ((p2 ∨ (p2 ∨ p3)) ∧ True)) ∧ ((p2 ∨ p4) ∨ p5))) ∧ (((p2 ∧ True) ∨ p1) ∨ p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3399083618278246954127697970 : ((p4 → False) → ((((True → p1) ∧ False) ∨ (p1 → ((p3 → (False → p3)) → ((True ∧ (p4 ∨ (p2 ∧ p5))) ∨ p5)))) ∨ (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_902801808221003491976251813639 : ((((((False ∨ False) ∨ True) → ((((p1 ∨ ((p2 ∧ ((p5 ∨ True) → p2)) ∨ p3)) ∧ True) ∨ p5) ∧ False)) ∧ (p5 ∨ (p5 ∨ (p1 ∧ p3)))) → p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : ((False ∨ False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158969388702167001948556868651 : ((p3 ∨ (((((False ∧ (p5 ∨ True)) ∨ p1) → (((p1 → p1) ∧ (p1 → True)) → p5)) → p1) ∨ False)) ∨ ((((p5 ∧ p5) ∨ p3) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42854094022023658295086173368 : (((p2 → ((p4 → ((((p4 ∧ (p1 → ((p2 ∨ p4) ∧ ((p2 ∧ True) ∨ (p3 → False))))) ∧ True) ∧ p4) → p2)) → (p5 ∨ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328274107208933749556323227336 : (True → (((((p1 ∧ (p1 ∧ p5)) ∨ (((False ∨ ((p5 → (p2 → p4)) ∨ False)) ∨ True) ∧ p1)) ∨ True) ∨ False) ∨ (p5 → (p1 ∧ (p5 ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46808678867524390708074581356 : ((((((((False ∧ (((True → p3) → ((p4 ∧ (p3 ∧ p2)) ∨ p5)) ∨ True)) ∨ True) → (p4 → p2)) → p4) ∨ p3) ∧ p1) ∨ (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192256940844474372407081644390 : ((((False → (p4 ∧ p5)) ∧ ((p4 ∨ p3) ∧ p5)) ∧ True) → ((p2 ∧ ((p2 ∨ (False ∧ p4)) → (p4 ∧ (((p4 → p3) → p4) → p4)))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229481692269302454544390452117 : ((p2 → (p3 ∧ False)) ∨ (((p2 ∨ True) ∧ p2) ∨ ((p4 ∨ p4) ∨ (((p5 ∧ (p2 ∧ p3)) ∧ True) → ((p2 → (p2 → p5)) ∧ (p3 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309623734262566643423010154374 : (p2 ∨ (((p1 ∨ ((p3 ∨ p2) → ((((((p1 ∧ p3) ∧ p4) ∧ p3) ∨ True) ∧ True) ∧ p5))) ∨ (p4 → (True → True))) ∨ ((p5 ∨ False) ∧ p5))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142358502691730873186274859950 : ((p3 ∧ (p5 ∧ (p1 ∨ (((False → ((p4 ∧ p3) → p3)) ∨ True) ∨ ((p3 ∨ True) → (p5 ∨ (p5 → (False ∨ p3)))))))) → ((p2 ∨ False) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55770938861146789423081179766 : ((((p1 ∨ p1) ∧ (False → p1)) ∧ ((p3 ∧ (p1 ∧ (p3 → (p2 ∨ (p4 → p5))))) ∧ (p3 → (((p3 ∨ (p5 ∨ False)) ∨ p2) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115876226740174911718237822002 : ((((False ∧ (p3 ∧ p3)) ∧ p4) ∨ (True ∧ ((((p2 ∨ p4) ∧ ((p5 ∨ p1) ∨ p3)) ∧ (p1 → (False → (False ∨ True)))) ∧ True))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327898401195504870833445752211 : (True → ((p1 → (((((True ∨ ((p2 ∧ (p5 ∧ p3)) ∧ p2)) → True) ∧ ((p4 ∨ (p1 → False)) ∨ True)) ∧ p5) ∨ (p5 ∨ p3))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115365247740925154579685030995 : (((((((p1 ∨ p4) ∧ p4) ∨ p1) → p4) → p1) ∧ ((((p1 ∧ (p4 ∨ p5)) → p4) ∨ (True ∨ (p2 ∧ p5))) ∨ (False ∨ p1))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41369167988557989154949216094 : ((((((p3 ∧ p1) ∧ False) ∨ (((p1 ∨ True) → (((p1 → p2) ∧ p5) → p4)) ∨ p5)) → ((p4 → p1) → ((p5 → p2) → p1))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135729121325369881337626815647 : ((((((p2 ∧ p4) ∧ p2) ∨ ((((p2 ∨ p1) ∨ p3) → False) ∨ True)) ∨ p3) ∨ ((p3 → (p5 → (True ∧ True))) → p2)) ∨ (True ∧ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47261859934205259710877279981 : (((((True ∨ True) ∨ ((p4 ∧ p4) → p1)) → ((p2 → ((((p2 ∧ False) → (p5 → p1)) ∨ p4) → False)) ∨ (p5 ∨ True))) ∨ (p4 ∧ p1)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
theorem thm_5_vars_164511429487865582880426923520 : (((((p5 ∧ p3) ∧ (False ∧ (((p1 ∧ (p2 ∨ p3)) → p2) ∧ True))) ∧ (True → p1)) ∧ p5) ∨ (p4 → (((True ∨ p5) ∨ (p3 ∨ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191011545436587743235133835103 : (((p2 ∨ ((p1 ∧ True) ∨ p3)) ∨ (p4 ∨ (True → p1))) ∨ ((False ∧ p1) → (p4 ∨ (p1 ∨ (((True ∧ p5) → ((p2 → p5) ∧ True)) → p5))))) := by
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
theorem thm_5_vars_51372069414773083345710682432 : (((((((p1 ∧ (p5 ∨ (((p4 ∨ p2) ∨ True) ∧ p4))) ∧ True) ∧ (p3 → p2)) ∧ True) ∨ p4) → (True → ((False → (p5 ∧ p2)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649035718798376955599162494067 : ((((((p3 ∨ (p5 ∧ (p4 → ((True → ((True ∨ (p1 → ((p3 ∧ False) → p4))) ∧ True)) ∧ False)))) ∨ (p4 ∧ p1)) → p3) ∧ (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157906717936934678051926042270 : ((((((p1 → p1) ∧ p5) → (False → p2)) → (True ∧ False)) → (True → (False ∧ (p1 ∨ (p3 → p5))))) ∨ ((False → p2) ∨ ((p2 → p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726091241727525352667626741523 : (((((p1 ∧ p3) ∨ False) ∨ (((p3 → (((p3 ∧ p3) → (True ∨ p5)) → p2)) → (p3 ∧ True)) ∨ (p4 ∨ ((p3 → (True ∧ p2)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877065610566500039037119991273 : ((((((True → True) ∧ (True → ((((False ∨ False) → True) ∧ p2) ∧ p1))) ∨ ((False → False) → ((p5 ∧ (True → p2)) → p1))) ∧ (p5 ∧ p2)) → p1) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h3.left
    let h14 := h3.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h15 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h17 := h12 h15
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : (p5 ∧ (True → p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h13
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h18
    -- One of the premise coincides with the conclusion.
    exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694510689028959281095175876702 : ((((False ∧ ((True ∧ ((((True → p3) ∨ p4) ∧ False) → (p4 ∧ False))) ∧ True)) ∨ ((((False → p1) → p5) ∧ (False ∧ (False ∨ p3))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358754938336347233142337822345 : (p5 → (p5 → (p5 → ((((p2 → p3) → p1) ∨ ((p2 → p5) ∧ (((p3 ∧ ((p5 → p5) → p3)) → p5) → ((False ∨ p3) ∨ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41613165619164802057508361068 : ((((p1 ∨ (p3 ∨ ((p4 ∧ p3) ∧ (False → p5)))) ∨ ((((False → p1) → p5) → (((False ∨ (False ∨ p2)) ∧ p2) ∧ p2)) ∨ True)) ∨ p5) ∨ p1) := by
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
theorem thm_5_vars_178027436437890718856702076854 : (((p3 → (p4 ∧ ((p1 → (p4 → p3)) → ((False ∧ p4) ∨ p4)))) ∨ True) ∨ (p3 ∨ (p4 → (((p5 ∧ False) ∨ ((True ∧ True) → True)) ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684166271430691964732981267832 : (((((((p2 ∧ p3) ∧ p5) ∨ (p4 ∧ (((p3 → p3) ∧ p5) ∨ (p1 → p5)))) ∨ (p4 ∧ True)) ∨ (((p1 ∧ (p2 ∧ False)) ∧ p4) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40347802408331006149712907287 : (((((p3 → ((((p3 → False) ∧ p1) → p3) → ((True → (p5 → (((False ∧ p5) ∨ (p2 ∧ p4)) → p4))) ∧ p4))) ∨ p1) ∨ p5) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773428269337867988095206159141 : (((False ∨ (((True → (((((p2 → (p1 ∧ False)) ∨ p3) ∨ (False ∨ ((False ∨ True) ∨ ((False ∧ p3) ∨ p2)))) ∧ False) ∧ p1)) ∧ p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206136164514360746298600337962 : ((p4 ∧ (True ∨ (p3 ∨ (True → p5)))) ∨ (((p3 ∧ (((p1 ∨ (True ∨ (True ∨ True))) → (p3 → p4)) ∧ ((False ∨ p2) ∨ True))) → p4) ∨ p3)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h9 : (p1 ∨ (True ∨ (True ∨ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h9
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h12 := h10 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h14 : (p1 ∨ (True ∨ (True ∨ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h15 := h4 h14
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65171390781011993621696532910 : ((p3 ∨ (((False ∨ ((((((p4 ∧ True) ∧ ((p2 ∨ p2) ∨ True)) ∧ (p1 ∧ True)) ∨ p4) ∧ p4) ∧ p4)) ∨ (p4 ∨ (p3 ∧ p3))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184970039591109727325763525767 : (((p5 ∧ (p2 → p2)) → (p4 ∨ ((p2 → (p4 ∧ p5)) ∨ False))) ∨ ((p3 → (((p5 → p2) ∨ p5) → True)) → (False → (p2 ∧ (True ∧ p3))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207916020146234921560184068469 : (((p5 ∧ (p5 ∨ p4)) ∧ (p1 ∨ p5)) → (False ∨ ((((p4 ∧ (p4 ∧ ((p2 → True) ∨ (p4 ∧ (p1 → (p1 ∨ p2)))))) ∧ False) ∧ p5) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651489576657667256191677794219 : (((((True ∧ p4) ∧ ((p2 ∧ ((True ∧ (False ∨ p3)) ∧ ((p2 ∧ ((True → True) ∧ p5)) → p4))) ∨ ((True ∨ p4) ∨ False))) ∧ (p3 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618671072919226010858480268 : ((((p5 ∧ ((False ∨ False) → (((p1 → p5) ∧ (True ∨ p5)) ∧ (False ∧ ((p1 ∧ (False ∧ p5)) → p5))))) → p3) ∨ (p5 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40625970528666091044193618180 : ((((((False ∧ (p4 → (False ∨ ((p1 ∧ p2) ∨ (((p4 ∧ p5) ∧ ((True → p4) ∧ (False ∧ True))) ∧ p1))))) ∧ p3) → True) → p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663239355352411272457043641424 : (((((p3 ∧ False) ∨ ((p2 ∧ ((p4 ∨ (p1 ∨ True)) ∨ (((p1 → False) ∨ (((p2 → False) ∧ p3) ∨ p4)) → p4))) → p3)) → (p1 ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168842031404470259295000989997 : ((p3 ∨ (((p4 → ((p1 → p5) ∨ True)) → p1) → ((True → False) ∧ ((p5 → p3) ∧ p1)))) → ((p1 ∨ p3) → ((p3 → (False ∧ p3)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : ((p4 → ((p1 → p5) ∨ True)) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
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
    cases h1
    case inl h17 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h18 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42029854296382238422234868078 : ((((p2 ∧ p3) ∨ ((((((p5 → (p1 → p2)) → True) → (p2 → (p4 ∧ (p3 ∨ p1)))) ∧ False) ∨ p3) ∨ ((False ∧ False) → p4))) ∨ p1) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119945034382044935610695761970 : (((((((True ∧ (((p1 ∨ (((p4 → False) → p4) → p3)) → p5) ∨ p3)) → False) ∨ True) ∧ p3) → ((p3 ∨ True) ∧ True)) ∧ p1) → (p5 ∨ True)) := by
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
theorem thm_5_vars_200159214279496758888746997191 : ((((p3 ∨ p5) ∨ p5) ∨ (False → (p2 → p1))) → ((((((p2 → False) ∨ (p4 ∨ p1)) ∧ ((p5 → p4) ∧ p4)) ∨ (p4 → p4)) → False) → p2)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h6 : ((((p2 → False) ∨ (p4 ∨ p1)) ∧ ((p5 → p4) ∧ p4)) ∨ (p4 → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h8 := h2 h6
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : ((((p2 → False) ∨ (p4 ∨ p1)) ∧ ((p5 → p4) ∧ p4)) ∨ (p4 → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h12 := h2 h10
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : ((((p2 → False) ∨ (p4 ∨ p1)) ∧ ((p5 → p4) ∧ p4)) ∨ (p4 → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h14
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : ((((p2 → False) ∨ (p4 ∨ p1)) ∧ ((p5 → p4) ∧ p4)) ∨ (p4 → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h18
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1502118211260290013640702191 : ((((True → False) ∨ ((p1 → ((p5 ∧ (False ∧ (p4 → ((True → False) → True)))) → True)) → False)) → (p1 ∨ (p4 ∧ p2))) ∨ (True ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → ((p5 ∧ (False ∧ (p4 → ((True → False) → True)))) → True)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h6
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353436707734051269682584025021 : (p4 → (p1 ∨ ((p2 ∧ (p1 ∨ (p4 ∧ (p3 ∧ (True ∧ p1))))) → ((False ∨ ((False → p2) ∧ False)) ∨ ((((False → p3) ∨ p5) ∧ p5) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h22 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112240126717923022496180473223 : (((p3 ∨ (((((False ∧ False) ∧ p2) → ((p4 ∧ (((p5 ∧ True) ∧ ((p5 → p2) → True)) ∧ p1)) ∧ False)) → p3) ∨ True)) ∨ p2) ∨ (p1 ∨ False)) := by
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
theorem thm_5_vars_750293629760139125098538870567 : (((True ∧ ((p2 ∨ (True ∧ (((p4 ∧ p1) ∨ ((p1 → p2) ∨ p2)) ∨ (p5 ∧ (((p5 → p3) ∨ p1) → (p2 ∨ p3)))))) ∨ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40250577313822104279717965298 : ((((False ∨ ((p5 ∨ (p1 ∧ ((((((p1 → (p3 → p3)) → p1) ∧ p1) → (True ∨ p4)) ∧ False) ∨ p4))) ∧ (p5 ∧ p3))) ∧ p5) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117901270175182625838820867964 : ((p5 ∧ (((p1 ∧ (p2 ∨ (p5 → (((p1 → p2) → (True ∧ True)) → p2)))) ∧ (p1 ∧ p3)) ∨ ((p4 ∧ (p5 ∨ False)) → False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354923496899534192265396500725 : (p5 → ((p2 ∨ ((((p3 ∨ p1) → (True → (((p1 → p3) ∧ (p2 → p1)) → True))) ∧ True) → (((p2 → False) ∧ True) ∨ (p4 → p4)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136594568548488877587556196415 : (((p2 ∨ (p4 ∧ p3)) ∨ (p5 → (p3 ∨ ((((p4 ∧ p2) → (p2 ∧ (p5 ∨ True))) ∧ p2) → (p3 ∧ (p5 ∨ p4)))))) ∨ (p3 → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264186187343817847873286266481 : (True ∧ (((((p5 ∨ p1) ∧ (p5 ∧ p5)) ∨ p1) ∨ False) → ((((p3 ∧ True) ∨ ((((p3 ∨ p4) → p2) ∨ p5) ∨ p3)) ∧ (p2 → True)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h5.left
        let h8 := h5.right
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
        -- One of the premise coincides with the conclusion.
        exact h8
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h5.left
        let h12 := h5.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148296055648614494575470702098 : ((((((p5 ∨ False) ∨ p2) ∧ ((p2 → False) ∨ p3)) → (((True → False) → p5) ∨ p1)) → (p4 ∧ (p3 ∧ p4))) ∨ ((p5 → (p5 ∨ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61126867594483148037544426140 : ((False ∧ ((((p5 ∧ p5) → ((p5 ∧ p3) ∨ p1)) ∧ p4) ∧ ((((p5 ∧ p1) ∧ (False ∨ ((p4 ∨ p2) → p4))) ∧ (p1 ∨ p2)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219497662879188546441945626538 : ((p5 ∨ ((False ∨ p4) ∨ p1)) → (((p3 → p5) → ((p4 ∨ p4) ∧ ((p1 → p5) → ((p1 ∨ True) ∧ p4)))) ∨ (p5 ∨ (p4 → (p1 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_514919356754310065502651182994 : ((((p5 ∨ p1) ∨ (p1 → ((p1 → (True ∧ (p4 ∨ ((p3 ∨ (False → p5)) ∧ p4)))) ∨ ((p2 ∧ ((False ∧ True) ∨ p3)) → (p5 ∨ p3))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705922146327454623808771194882 : (((((p5 ∨ (p2 → False)) ∨ ((p2 → p2) ∨ True)) ∧ (((((p1 → p3) ∨ p2) ∨ False) ∨ (True ∧ (p5 ∨ p5))) ∧ (p3 → (p3 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42357198160291617147496070014 : (((p3 ∧ (False ∧ (((p4 ∧ (((p5 ∨ ((p2 → True) ∧ ((True ∨ False) ∧ p4))) ∨ p2) ∧ (p3 ∧ (p2 ∨ p1)))) ∧ False) ∨ p1))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56986105222034225041248648953 : (((p4 ∨ (p5 → p4)) ∧ ((False ∧ ((((p5 ∨ p1) → p3) ∧ ((p4 → (p2 → (p5 ∧ (p2 ∨ True)))) ∧ p1)) ∧ True)) ∧ (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62710708271776124580826595377 : ((p4 ∧ (((p2 ∧ p5) ∨ ((((p3 ∧ False) ∨ p5) ∧ (((p1 ∨ p2) → ((p1 ∧ (p3 ∨ p4)) ∧ p5)) ∨ p1)) ∧ (True → p3))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317734928860960305989277550033 : (p4 ∨ ((((p2 → False) ∨ (((p3 ∨ p2) ∨ ((p2 ∨ ((p3 → ((True ∧ p4) ∧ p5)) ∨ p2)) ∧ p1)) → p4)) ∨ (True ∨ (p5 → p1))) ∨ p4)) := by
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
theorem thm_5_vars_118189577140357493486292952211 : ((False ∨ (p2 ∨ ((p5 ∧ ((p3 ∧ (False ∨ p5)) ∨ (p5 ∧ True))) ∨ (p3 → (p2 ∧ ((((p2 → False) → True) ∧ p1) ∨ p1)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233490571215958539260538907370 : ((p1 ∨ (p2 ∧ False)) → ((((False ∧ p1) ∨ (True ∧ (p3 ∨ (((p1 ∧ (p5 ∨ True)) → ((p4 ∧ p1) ∨ (p1 → p2))) → p4)))) ∨ p3) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722134008055193058512444384771 : ((((p3 → ((p3 → True) → p2)) → ((p5 → ((p4 ∧ ((True → p1) ∨ ((((p3 ∨ (p2 ∧ p4)) ∨ p5) ∨ p2) ∨ p3))) ∨ p4)) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759762616610045499596614641564 : (((p2 ∧ (((((True → (p3 ∨ p2)) ∧ True) ∨ (p5 ∨ p5)) ∨ p4) ∨ (p2 ∧ (p5 ∨ (p2 ∧ ((p1 ∨ p5) ∨ ((True → p2) ∧ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300550882179529091247891546437 : (False ∨ (((((p3 → ((False ∧ p3) ∧ (p3 → p4))) ∧ (p1 → p2)) → p5) ∨ (p1 ∧ ((True ∧ p2) ∨ p1))) ∨ (p3 → ((True → False) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56194962858753274610367059537 : (((p5 ∧ (p4 ∧ (p4 ∨ True))) ∨ (p2 → (p2 → (((True ∧ (False ∨ ((p2 ∧ p5) ∨ (p3 ∧ (p1 ∧ True))))) ∧ (p3 ∨ p1)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184151402122047039074144822936 : (((p1 ∨ (((False → p1) ∨ p5) → ((p2 ∨ p2) ∧ p3))) ∨ p1) ∨ ((p3 → ((((p3 → False) ∧ p4) → (p1 ∨ (p2 ∧ True))) ∨ False)) ∨ p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702396797493268513983276174672 : (((((((p2 ∨ False) ∧ p5) ∧ (True → (p1 ∨ p5))) ∨ p5) ∨ (p1 ∨ (p2 → (((False → (False ∧ p2)) ∨ (True ∧ (p5 ∧ p4))) ∨ p1)))) ∨ False) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62733270820883156682466980303 : ((p4 ∧ ((p3 ∨ (p5 ∧ ((False → False) → ((((((p3 ∨ False) ∧ p3) ∨ p5) → (p1 ∨ (p2 → p1))) ∨ p2) → False)))) ∧ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207883558223721497208588659294 : ((((p1 ∨ p3) → p5) ∧ (False ∨ p5)) → ((p5 ∧ (True ∨ p4)) ∧ ((p1 → p4) ∨ (((p1 → p4) ∨ (p4 → (True ∧ (p1 → p5)))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219250959807080411728485401357 : ((p1 ∨ (True ∧ (p3 ∧ p5))) → ((((((p1 ∨ (((False ∨ p4) → True) ∧ p2)) → p2) → (p1 ∨ p1)) → ((p4 → p2) ∨ False)) ∨ p4) ∨ True)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66188000851621181602537108872 : ((p5 ∨ (((False → False) ∧ ((((p2 ∧ p4) → p1) ∨ ((False → (False → p2)) ∨ (p1 ∧ p2))) ∧ p5)) → ((p1 ∧ p1) ∧ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351407960147302884536414902287 : (p4 → ((((p5 → (False ∨ (p1 ∨ (p5 → p3)))) → p4) → (p1 ∧ (True ∧ (False ∨ ((p5 ∧ p4) ∨ p5))))) ∨ ((True → p4) ∧ (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175064599971232589724310999109 : ((p2 ∧ (False → (p2 → ((p1 ∧ p1) ∧ ((p1 ∧ ((p1 ∧ False) ∨ p1)) ∨ p5))))) → ((p5 ∨ (p3 ∨ p3)) → (((False → p4) → p1) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h1.left
      let h9 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h1.left
      let h12 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165480259734671495373009348656 : ((((p4 → ((p1 ∨ ((p2 → p3) → p3)) → False)) ∨ p5) ∨ (False ∨ (True ∨ (True → p3)))) ∨ (p3 ∧ ((p3 ∧ p5) ∨ (p4 ∨ (p4 ∧ p4))))) := by
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
theorem thm_5_vars_42563481607584240517560756704 : (((p1 ∨ (p4 → (((p1 → (p2 ∨ p4)) → (False ∨ (p2 ∧ ((((p2 → (p5 → (False ∨ p2))) ∧ p5) ∧ p1) → True)))) ∨ p5))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61775385837652985741375418923 : ((p2 ∧ (((p5 ∧ (((((p5 ∧ p1) ∧ p5) ∨ p3) ∨ p1) → True)) → ((False → p3) → (((False ∨ p2) → (False ∨ p2)) → False))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46321525480980403190981772272 : ((((((False ∨ p3) ∧ p2) ∧ ((p5 ∧ p5) ∧ ((p3 → (p3 → p1)) ∧ (p2 ∨ p4)))) ∨ (p2 ∨ (p2 → (p1 ∧ False)))) ∧ (p4 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634586300694662720679537215310 : (((((p2 ∧ (p3 → (((p1 ∧ (p1 → True)) ∨ (((p5 ∨ (p5 → True)) ∧ p2) → (p5 ∧ p5))) ∨ p4))) ∧ (True ∨ (False → p3))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66752976026297320543977522280 : ((True → (p1 ∧ ((p5 ∧ ((True ∧ p4) → p5)) ∧ ((p4 → (True ∨ ((p1 → (True ∨ p3)) ∨ p4))) → (p3 ∧ ((p3 ∨ p2) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204563686558247344672732740558 : ((((p3 ∧ True) ∧ (False → p2)) ∨ p5) ∨ ((p3 ∨ ((p2 ∧ False) → ((False ∧ (p1 → False)) → False))) → (((p2 ∧ (p4 → p3)) ∨ True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147864137239563724786353840267 : (((p1 → (p5 → ((((True → ((True → ((True ∨ (True ∧ p5)) ∨ p2)) ∨ p1)) → p1) ∧ True) ∧ p1))) → p3) ∨ (p1 → (False → (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310840120418479114857243970001 : (p2 ∨ (((p5 → p1) ∧ p2) → (((((p3 ∧ p1) ∧ True) → (p3 ∨ ((p2 → (p2 ∧ ((True → p1) ∧ (False → p1)))) ∧ False))) → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_55654143193276679752404610711 : ((((False ∧ (p3 → p4)) ∧ p4) ∧ ((((((p4 → p5) → p2) → ((True ∧ p3) ∧ False)) ∧ (p4 → p2)) ∨ (p3 ∧ (True ∧ False))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125130080189985325171625000766 : ((((True → p5) ∧ p1) ∨ (((True → True) ∨ p5) → ((p3 ∧ p2) ∧ (((p1 → ((False → True) ∨ False)) ∧ p2) ∧ (p1 ∧ p5))))) → (p4 ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((True → True) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149585196828144048095264709688 : ((p3 ∧ (((p1 ∨ (p4 → (p1 ∧ p1))) ∧ (False ∨ ((False → (p2 ∧ p3)) ∧ (p5 ∧ (p3 ∧ p3))))) ∨ False)) ∨ (True → (p2 → (p3 → True)))) := by
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
theorem thm_5_vars_161582810542776797650337501192 : ((True ∨ (((False → p2) ∨ (p3 → True)) ∧ (True ∨ (p3 → (p5 ∨ ((True → p1) → (False → p4))))))) → (False ∨ (p2 → (p1 → (p4 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- Implications on the right can always be decomposed.
        intro h26
        -- True on the right can always be proven directly.
        apply True.intro



