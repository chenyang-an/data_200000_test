variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41810621419995115682752146573 : (((((p4 ∧ p5) ∧ p2) ∧ (p1 → (((p2 ∨ (False → p2)) ∨ ((p1 ∨ p1) → ((p4 ∨ True) → (True → p5)))) ∧ (p3 ∨ False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158897135372562367570878602913 : ((p1 ∨ ((p1 → (p2 ∨ ((p3 ∨ (p2 ∨ (((p5 ∨ (False ∨ p4)) ∧ p2) ∧ p5))) ∧ p1))) ∨ True)) ∨ ((p5 → (p2 ∨ (p1 ∨ p1))) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70851188131258966750460007171 : ((((True → (False ∧ (p2 ∧ (False → (((True → True) ∧ p5) → True))))) ∧ ((True ∧ (p3 ∨ (False ∧ p5))) → ((p2 ∨ p5) → False))) ∧ p4) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785712498994740837466289143038 : (((p4 ∨ ((((p3 ∧ ((p5 ∨ p5) ∨ p4)) ∨ ((p4 ∧ (p1 ∧ p1)) → p4)) ∧ (p4 → (p5 → (((p2 ∨ p3) ∧ True) ∨ p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355018480414645781061239106780 : (p5 → (((True → ((((p4 ∨ p2) → ((p4 ∨ p1) → (((p4 → ((p4 → (p1 ∧ p4)) → False)) → p4) ∨ p5))) ∧ False) ∧ p4)) ∧ True) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174550508502975819731903826223 : (((((False ∨ True) → p3) ∧ True) ∧ (((((True ∨ p3) ∧ True) ∧ False) → p5) ∨ p5)) → ((p3 ∧ p3) ∧ (p5 ∨ ((True ∧ False) ∨ (False → True))))) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h10 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h16 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h17 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h17
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h20 : (False ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h21 := h14 h20
    -- One of the premise coincides with the conclusion.
    exact h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h27
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h28 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h29
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233065198528392240021937589372 : ((p4 ∧ (p3 ∨ p2)) → (((p5 → (False ∨ p1)) → False) ∨ ((((p1 ∨ p4) → False) ∧ p4) → (((p2 ∧ p3) → (p5 → p1)) ∧ (p1 ∧ p1))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h17 := h14 h16
    -- False on the left can always be used.
    apply False.elim h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h5.left
    let h19 := h5.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- False on the left can always be used.
    apply False.elim h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h24.left
    let h27 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h23.left
    let h29 := h23.right
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h30 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h31 := h28 h30
    -- False on the left can always be used.
    apply False.elim h31
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h32 := h23.left
    let h33 := h23.right
    -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
    have h34 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33
    -- We have shown the premise of h32, we can now drive its conclusion.
    let h35 := h32 h34
    -- False on the left can always be used.
    apply False.elim h35
    -- Conjunctions on the left can always be decomposed.
    let h36 := h23.left
    let h37 := h23.right
    -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
    have h38 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h37
    -- We have shown the premise of h36, we can now drive its conclusion.
    let h39 := h36 h38
    -- False on the left can always be used.
    apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245317986428688471040819324517 : ((p2 ∧ p2) ∨ ((True → p2) → ((((((p3 → p2) ∨ p2) → p5) ∨ p4) ∨ (p4 ∨ (True ∧ p2))) ∨ ((False → False) ∨ (p5 ∨ (True ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_133649915649132304298807080094 : ((((False ∧ ((p1 ∨ p5) ∧ (True → ((p5 ∨ (p5 ∨ ((False → (p2 → p3)) ∧ p4))) ∨ p3)))) ∧ (False ∨ False)) ∧ p4) ∨ ((p3 → p3) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305417617927513013048823768684 : (p1 ∨ ((p5 ∧ ((p1 ∧ (((True ∨ p1) ∨ p4) ∧ p5)) ∧ (p2 ∨ (p4 ∨ (p1 ∨ False))))) ∨ (((p5 ∨ (p3 ∨ (p5 → True))) ∨ p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244860266490325486468244624939 : ((p1 ∧ p2) ∨ ((True → ((((p3 ∨ (p3 ∨ (True ∧ p1))) ∨ p3) → p4) → ((p3 ∧ ((((p3 ∧ True) ∨ p2) ∨ p5) ∨ p5)) ∧ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774521978415963000649440011361 : (((False ∨ (((p4 → (False ∨ (False → p3))) → ((p2 ∧ ((p5 → p5) ∧ p3)) ∨ p2)) ∨ (p3 → (p2 ∨ (p2 ∧ (p5 ∨ (False ∧ False))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135723016971299376136103170667 : (((((p4 ∧ (p1 ∧ (((True ∨ p1) → (p3 ∧ p4)) ∨ False))) ∨ p3) ∧ False) ∨ (p3 ∨ (((p3 ∨ False) ∨ p1) → False))) ∨ (True ∨ (p5 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59948852654989329921715465696 : (((True ∨ p2) → ((p1 → ((p5 ∧ (p5 ∧ False)) ∧ True)) ∧ (p3 ∨ (((p4 ∧ p1) → (True ∧ (p3 ∧ False))) ∨ (False → (True ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314638165770263227712493285077 : (p3 ∨ ((((p2 → (p3 ∧ (((p3 ∧ p3) ∨ (p3 ∨ (True ∧ p4))) ∨ p3))) ∧ p2) ∧ p4) ∨ ((p4 ∧ False) → (((p5 ∧ p5) ∧ p2) ∨ p3)))) := by
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756924429372992732477840061456 : (((p1 ∧ (((((p3 ∧ True) → p3) ∨ p4) → False) ∨ (((True → True) ∨ ((((True ∨ (p3 → (p3 ∨ p1))) → True) ∧ False) ∧ p5)) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57661046122715219903859612906 : ((((p4 ∨ p3) ∨ p4) → ((p5 ∧ ((p2 → ((p1 ∧ p4) → p4)) ∨ p1)) → (((False ∧ (p4 → (p1 → True))) → (p2 ∧ p2)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709778306450379213829412836093 : ((((p1 → (False → ((p1 ∧ (p3 ∧ p5)) → p2))) → (p5 ∨ ((p2 ∨ (False → (True ∨ False))) ∨ (True → ((p5 ∨ p1) ∧ (p4 ∧ p1)))))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630084842657682642939550920197 : (((((((False → p3) ∧ p4) → (p4 ∨ (p3 ∧ (((((p5 ∨ False) → p1) ∧ (p2 → p3)) ∨ ((p2 ∧ p3) ∨ p5)) → p2)))) ∨ False) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356866600347995445620661229591 : (p5 → ((p3 ∧ (p1 → (False ∨ p2))) ∨ (((((p3 ∧ p5) ∧ True) ∧ p2) ∧ False) ∨ (True ∧ (((True ∧ ((p1 ∨ p5) ∨ p1)) → p4) → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∧ ((p1 ∨ p5) ∨ p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_170031703595958048753523931799 : ((((False ∧ p4) ∨ ((((p4 ∧ p2) → False) ∧ p1) → p5)) ∨ ((p4 ∧ False) → p1)) ∧ (p4 ∨ (p4 ∨ (p4 → (((p1 → p1) → p4) ∧ True))))) := by
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
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312702531191427718668545713005 : (p3 ∨ ((((p2 ∨ True) → (((((False ∧ (False → p5)) ∧ ((p2 ∨ p2) ∨ p2)) ∧ p1) ∨ p1) ∨ p1)) ∨ ((False ∨ (True → False)) → p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322851868085952217794422093298 : (p5 ∨ (((True ∨ (((p1 → p4) ∨ (p2 → p5)) → p2)) → ((((p5 → (((False ∧ p2) ∨ p2) ∧ p3)) → p4) → p5) ∧ (p1 ∧ p5))) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((p1 → p4) ∨ (p2 → p5)) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132978118607247078044618770742 : ((p4 ∨ (p2 → (False ∨ (((p5 → ((((p1 ∧ ((p5 ∨ p5) ∨ False)) ∨ False) ∧ False) ∨ p4)) ∨ True) ∨ (p2 ∧ p2))))) ∧ ((p3 ∧ p1) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300960311627224328525163782433 : (False ∨ ((((p1 ∨ ((p3 ∨ p2) ∨ p2)) ∨ ((p4 ∨ p4) → p2)) → p2) ∨ (((False → p3) ∨ ((p1 ∨ True) ∨ (p1 ∧ (p3 → p5)))) ∨ p4))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52703497447647717515254410012 : (((p4 → ((((p1 ∨ (False → (False ∨ p2))) → p1) ∧ (p2 ∧ True)) ∧ p4)) ∨ (p4 ∨ ((((p1 ∧ (p3 ∧ p3)) ∧ p1) ∧ p5) → p1))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655590887846067624972075898063 : ((((((True → p3) ∨ (p5 ∧ ((((p3 → p5) ∧ ((p4 ∧ ((p5 ∧ True) ∧ p4)) ∨ p5)) ∨ True) ∨ p3))) → (True ∧ False)) ∨ (p5 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166556072411938532707390228194 : ((p5 ∨ ((False ∨ p5) ∧ (((((p2 → p3) → p1) ∧ False) ∨ (True → False)) ∧ (False ∧ p2)))) ∨ ((((p2 ∨ p2) → p5) ∨ p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225553963717423936845402684266 : (((True → p4) ∧ p4) ∨ ((((False ∧ ((((p3 → False) → p2) ∧ (False ∧ p5)) → True)) → p3) → ((p2 ∨ p1) → (False ∧ (p2 ∨ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324752633849052218338525544337 : (p5 ∨ ((p5 ∨ (p5 ∧ p5)) → ((p3 ∨ ((p3 → (((p4 ∧ p1) ∧ p3) ∧ p3)) ∧ True)) → (((p3 → True) ∧ ((p1 → p5) → p3)) ∨ p5)))) := by
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
    cases h1
    case inl h4 =>
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
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194781827509064493929804735967 : (((p5 ∨ (False → ((False ∧ p1) ∨ p3))) ∨ p1) ∧ (((p3 ∧ p5) → p1) ∨ (p2 → (False ∨ (((p4 → (p5 ∧ (p4 ∨ p2))) ∨ p1) ∨ True))))) := by
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
theorem thm_5_vars_201121345267551025689389088015 : ((True → (True ∨ (((p4 → p4) → p1) ∨ p5))) → (True → (((False ∨ p4) → ((p2 ∧ (True ∧ (False ∨ p5))) ∧ (p4 ∨ (p1 → False)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134901711498239662936891032621 : ((((((p3 ∨ (p1 ∧ (p4 ∧ p4))) ∨ (((True ∨ ((p4 ∨ p2) ∨ p2)) → p3) → p1)) → p1) ∧ p4) ∧ (True ∧ p4)) ∨ (p1 → (p4 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56882800290163260489595706572 : (((p2 ∧ (p4 ∨ p5)) ∧ ((True ∨ (((p5 ∧ True) → (p4 ∧ p4)) ∧ (p5 → ((p3 → p1) ∨ False)))) → ((p1 ∧ p4) ∧ (False → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171898995517166868584030537511 : (((p5 ∨ (((((p2 → p5) ∨ False) ∨ (p1 ∨ (False ∧ p1))) ∧ p2) → p4)) → p2) ∨ ((p3 ∨ (True ∧ (p2 ∧ p1))) ∨ ((p1 ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328285101563328819872164976263 : (True → (((((p1 ∨ (p4 ∨ p1)) → ((((True ∧ (p4 ∧ p1)) ∧ p2) → True) ∨ p5)) ∨ p4) → (False ∧ p5)) ∨ ((p5 ∨ (p4 ∨ p2)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114458155527167338000388693801 : ((((p4 → ((p2 → ((p1 → p2) → p5)) → (False ∧ (((p3 → p4) ∧ False) ∧ p5)))) ∧ p4) → (p2 ∧ (p3 → (False ∧ p2)))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112592483294863475737278388958 : (((((((p3 ∧ p5) ∨ p3) → p4) ∧ (((p2 ∨ True) ∧ (((p4 → p4) → p2) ∨ True)) ∧ (True → True))) ∧ (p1 → p2)) → p4) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198690731427189057397379772706 : ((p4 ∨ (p4 ∧ ((p4 ∧ True) ∧ (p5 ∨ p5)))) ∨ (((p2 ∨ p5) → True) ∨ (p1 → ((p4 → (((True ∨ False) → (p3 ∧ p1)) ∨ True)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135026459584245681692646703306 : (((p4 → ((True ∧ (((((False ∨ (p1 ∨ p4)) → p3) → (p4 ∨ p3)) ∨ p5) → False)) ∧ (False → p1))) ∧ (p2 ∧ p5)) ∨ (p1 → (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626549802774250170575103286467 : ((((p4 → (((p5 ∧ (True → True)) ∧ p2) ∧ (p1 → (p2 ∧ (p3 ∨ (p2 ∧ ((p2 ∧ (((p2 → True) ∧ p3) ∨ p4)) → False))))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810689623342491006290262376171 : (((p5 → (((p2 → p3) → p1) ∨ (((p2 ∨ ((p4 ∧ p5) ∨ ((p5 → ((p2 ∨ p4) ∧ p5)) ∧ (True ∨ False)))) ∨ (p3 ∨ p5)) ∨ False))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157383682197871658111630725251 : ((((p4 → (p2 ∨ (p3 ∨ ((p1 → (p2 ∧ (p3 ∨ (p5 ∨ p4)))) → False)))) ∧ p3) ∧ (p2 → p2)) ∨ ((True ∨ (p3 ∨ (p1 ∧ p5))) ∧ True)) := by
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
theorem thm_5_vars_55318456994633934603870359950 : (((p1 ∨ (p4 ∧ ((True → True) ∨ p4))) ∨ (p5 ∨ (((p4 → ((p2 ∧ p1) → False)) ∨ p5) → (p4 ∨ (p5 → (p1 → (True ∧ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114456304753947434908111593111 : ((((p3 ∧ (p5 ∨ (((p5 → ((p4 ∧ False) ∨ p1)) ∨ p3) ∧ ((p4 ∧ p4) ∧ p2)))) ∧ p2) → (p2 ∧ ((True ∧ p2) ∧ False))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609666696337293175159759070107 : (((((p1 ∨ (((p1 ∨ ((p5 → (((p4 ∧ (p5 → p2)) → (p3 → (p2 ∧ p2))) → p1)) → (False ∧ p3))) ∧ p2) ∨ p1)) ∨ p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213162726304235889668097282126 : ((((p3 ∧ p5) ∨ False) ∧ False) ∨ (p5 ∨ (((p4 ∧ (False ∧ (p5 ∨ ((False ∨ ((p3 ∨ True) ∨ p2)) ∧ (False ∨ (p5 → p3)))))) → p1) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780509111253781205966390304563 : (((p2 ∨ (((((True → p3) ∧ p3) ∨ ((False ∧ (p4 ∨ p1)) ∧ p2)) ∨ p5) ∧ (p2 ∨ (((p1 ∨ p4) → p3) → ((p4 ∧ p2) → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692160288398973120235389032145 : (((((((p2 ∧ p2) ∨ ((((p2 → False) → p2) → p2) → p5)) ∨ p4) ∨ True) ∧ (p2 → (p1 → ((False ∧ (p5 ∨ (p3 ∧ p2))) → p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60508303012656318471088753785 : ((True ∧ (((p5 → p2) → ((False → ((((False ∨ (p1 ∨ ((p1 → p3) ∧ p5))) ∨ p4) ∧ ((p3 ∨ p2) → p1)) ∨ False)) → p3)) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227625038330761195684146709190 : ((False ∧ (p2 ∨ True)) ∨ ((((((p4 → (p3 ∨ (p2 ∧ (p4 ∨ True)))) → p4) ∧ p1) ∧ (p3 ∧ ((p4 → True) ∨ p5))) ∨ p4) → (p2 → p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h11 : (p4 → (p3 ∨ (p2 ∧ (p4 ∨ True)))) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h11
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : (p4 → (p3 ∨ (p2 ∧ (p4 ∨ True)))) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h17 := h6 h15
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349293750563180037457845945078 : (p3 → (p2 → ((p5 ∨ (((p1 ∧ (p1 → (p3 ∨ ((p4 ∧ (p4 → p5)) → p2)))) ∨ p4) ∨ p4)) ∨ (((p3 → False) → False) ∨ (p3 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165221370021208379965234534652 : ((((((p2 ∧ (p4 ∨ p4)) ∨ p5) ∧ p4) → (((p5 ∧ False) ∧ False) ∧ p3)) ∨ (p1 → p1)) ∨ (((True → (p4 ∨ True)) → False) → (p3 ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165463695294105377782217131522 : ((((False → p1) → ((((p3 ∨ p5) ∧ True) ∧ p4) → p2)) ∧ ((p5 → True) ∧ (False → p2))) ∨ ((True → p4) ∨ (p2 → (p3 → (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_875633826012095524961629084 : ((True → ((((p5 → True) ∧ False) ∨ p2) ∨ ((p5 → (((p2 → False) ∨ (p1 ∧ False)) ∨ p5)) ∨ (((False ∨ p1) ∨ False) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50965070572807040693978897704 : ((((p2 ∧ (p2 ∧ (p3 ∨ p1))) ∧ ((p3 ∨ (p1 ∨ p2)) → (((p2 ∨ p1) ∨ p5) ∨ p4))) ∧ ((p2 ∨ p2) ∨ (p3 ∨ (False ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645530947924841259045768310349 : ((((p4 ∨ (p1 ∨ (p2 → (p4 ∧ (((p5 → p1) ∨ (((p2 ∨ p2) ∨ p5) ∧ p3)) ∧ ((False → p4) → ((p3 → p4) → p1))))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261906851487277640259144122468 : (True ∧ ((((((p4 → p2) → p4) ∨ p3) ∨ p5) ∨ ((((((True → p5) → ((p2 ∧ p4) ∧ p1)) → p2) ∧ p5) → p5) ∨ (p4 ∨ False))) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260709124822940401144235811917 : ((p3 → p4) → ((((False ∧ True) → p5) → ((((((p2 → (p4 ∨ (p4 ∨ (False ∨ (True ∧ False))))) ∧ True) ∧ False) ∨ False) ∧ p4) ∧ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46675027738336009760137722992 : (((p1 ∨ ((p5 ∨ False) ∨ (((((p5 ∧ p3) ∨ p2) ∨ ((p1 → True) ∨ p1)) ∨ ((False → p2) ∧ p2)) ∨ (p4 ∧ p4)))) ∧ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797244493848150143700192110193 : (((p1 → ((((True ∧ (False ∨ ((((((p3 ∧ False) ∧ p4) → p2) ∧ p5) ∧ (p4 ∨ (p4 ∧ False))) → p3))) ∧ (p1 ∨ p2)) ∨ p1) ∨ p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184398527119645634821519642947 : (((((p2 ∧ ((p4 ∨ p5) ∧ p1)) ∧ p3) ∧ p1) ∧ (p1 ∧ False)) ∨ (((p5 ∧ p1) ∨ (p1 ∨ (p2 ∧ (p3 → (p4 ∨ p3))))) → (True ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45949776041402257469056093342 : (((p5 → (((p3 ∨ (True → ((((p4 ∨ p3) ∨ p5) → p3) ∨ (p5 ∨ (p2 → p2))))) ∧ False) ∧ (((p1 ∧ False) ∨ p4) ∧ p5))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138300111690086619977841298090 : ((p3 → (((((p2 ∧ p4) → True) → (p1 → (False → False))) ∧ ((p1 → p3) → True)) → (p3 ∧ ((False → p5) → p4)))) ∨ (p1 → (p1 ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148861314579354034803981065483 : (((p2 ∨ (True ∧ (True ∨ True))) ∧ ((p1 ∨ p5) → ((((p3 ∨ p5) ∨ p3) ∨ ((p5 → p1) ∨ True)) ∨ False))) ∨ ((p1 → False) → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610715775835602934129419495940 : ((((((False ∧ (p3 ∧ ((((((False ∨ p2) → (p1 ∨ (p5 → p2))) ∧ p2) ∧ True) → p4) → False))) ∨ (p5 → (p2 → p5))) → p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179217027848499045327051512451 : ((p4 ∧ ((((p3 ∧ p2) → p4) ∧ (False ∨ p5)) ∨ ((p3 ∧ True) ∨ False))) ∨ ((False ∧ (p3 ∧ (p5 ∧ (p5 → (p4 ∨ True))))) → (p1 ∨ p4))) := by
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
theorem thm_5_vars_64006276962393692268267185736 : ((False ∨ (((False ∧ p5) ∨ (((True ∧ ((p2 → p2) → ((p2 ∨ p2) ∨ (False ∧ p5)))) → True) ∨ (p2 ∨ (True ∧ p4)))) ∧ (False ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623077583226551982284662281662 : ((((p5 ∧ (p3 → (((False ∧ True) ∧ (((p3 ∨ p3) ∧ (False ∨ True)) ∧ ((p1 ∨ (False ∨ ((p1 ∧ p5) ∨ False))) ∧ p5))) ∨ p1))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197831508454564707904079597007 : (((p4 ∧ (p2 ∧ p4)) ∨ (p5 ∧ (False ∧ False))) ∨ (((p3 ∧ (True ∨ (((p5 ∧ (p3 ∧ p2)) → p3) → (p5 → (True → p4))))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40280927158596256401942861887 : ((((p1 → (((False ∨ (False ∨ False)) ∧ p1) ∨ (p5 ∧ ((p4 → p1) ∨ ((False ∨ ((p1 ∨ (p4 ∧ p4)) ∨ p5)) ∨ p1))))) ∧ p3) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208775109222545487645071008001 : ((p2 ∧ ((p1 ∨ p5) ∧ (False ∨ p4))) → ((((((p1 ∧ p1) ∨ (p1 ∨ False)) ∨ False) ∧ ((True → (p1 ∨ (True → p5))) → True)) ∨ p4) ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45875352418597231380335594298 : (((p3 → (((((False ∧ p3) → False) → True) ∧ (p5 ∧ False)) ∧ ((False ∧ (p1 → (p3 ∧ (p4 ∨ p2)))) ∧ ((True ∨ p2) ∨ p4)))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762805060401015064753085854767 : (((p3 ∧ ((((p1 ∨ (True → (p5 ∨ False))) ∨ p2) → p4) ∨ (((True ∧ (p4 ∧ ((p2 ∨ True) → p4))) ∧ ((p3 → p2) → True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53630863153409732937561989377 : (((((p5 ∨ p4) ∨ (p2 ∧ p1)) ∨ (False ∧ (p4 → p3))) ∧ ((((p3 ∨ p1) ∨ p1) ∨ True) → ((((False ∧ False) → p3) ∧ p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136639910373628106807873443122 : ((((p1 ∧ False) → p3) → (p2 ∨ ((True → p3) ∨ (p4 ∨ ((p2 ∨ (((False → (True ∨ p4)) ∧ p5) → True)) ∨ p1))))) ∨ ((False ∧ True) ∧ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609488026806087238914194192872 : (((((p1 ∧ (((p1 ∧ p4) ∧ (p3 ∧ (p1 ∧ ((p5 → (p4 → (p4 ∨ (p3 → p4)))) → ((False ∧ p3) ∧ p4))))) ∨ p5)) ∨ p1) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_63885533779817795804262377806 : ((False ∨ ((((True → (p3 ∧ (((p4 → ((p4 ∧ p5) ∧ (p1 ∧ (((p3 → p2) ∨ False) ∧ False)))) ∧ True) ∨ p3))) → False) ∨ True) ∧ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_310496506298261674397430096781 : (p2 ∨ ((((p5 → p5) → False) ∧ (p5 ∧ p1)) ∨ (p2 → ((((False → True) ∨ (((p1 ∧ (True ∧ False)) ∧ (p2 ∧ p2)) ∧ p1)) ∧ False) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157622186775581669647547631208 : ((((((False ∧ p3) ∨ (p1 → (p4 ∨ p4))) → p1) ∨ ((False ∧ p3) ∨ p4)) ∧ ((p1 ∨ False) ∨ p1)) ∨ (p2 ∨ (((p1 ∨ p1) ∧ False) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187217345741155015159684247797 : (((False → p5) → (True → ((True ∧ p5) → ((True → p3) ∨ p5)))) → (((p4 → (p5 → p1)) ∨ (p5 → ((p2 ∧ p5) ∨ True))) ∨ (p5 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53253858363267189254802616331 : ((((p2 ∧ p5) ∨ ((False ∨ True) → (p4 → ((p5 ∨ p2) ∨ False)))) ∨ (((p2 ∨ p2) → (p2 ∧ (((p1 ∨ p2) ∧ True) ∨ p1))) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43494630058453638227845765090 : ((((p5 ∧ ((((False ∨ ((p3 ∧ (p1 ∧ (p5 → (p5 ∨ p2)))) → False)) → (p1 → (p1 ∨ p4))) ∧ p1) → (False ∧ p1))) ∨ p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191080428118808126538005869797 : ((((False ∨ p2) ∧ p1) ∧ (((p2 ∧ True) → False) → p3)) ∨ (False ∨ (((((p3 → ((False ∨ p4) ∧ (False → p2))) → True) → True) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150752424868652530808522034124 : (((((p1 ∨ p4) → ((((False → p1) ∨ ((p2 ∧ False) → p5)) ∨ p1) ∧ (p2 ∧ (p1 ∧ p5)))) ∨ p5) ∨ p4) → (((p4 ∨ p1) ∧ p3) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51188387139513556558338315376 : (((((p4 ∧ ((True → p5) ∧ ((True ∧ p3) → p1))) ∧ (p3 ∧ p1)) ∨ ((p5 → p3) ∧ p4)) ∨ ((True ∨ p4) ∧ (False → (p5 ∧ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148978360149107748354890142297 : (((False ∧ (p4 → p3)) ∧ (((p4 ∧ p2) → (False → (((p1 → False) → p4) ∧ (p3 ∨ p2)))) → (p1 → False))) ∨ ((False → p5) ∨ (p1 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693073502059007840580096520982 : ((((p1 ∧ ((p1 ∨ p2) ∨ (((True ∨ (p1 ∨ p3)) → (p3 ∨ p3)) → False))) ∧ (((p1 ∧ (p3 ∨ (p5 → p3))) ∨ (p1 ∨ True)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68342662540578339357159742358 : ((p3 → ((((p3 → p3) ∨ (True → ((p2 ∧ p1) ∨ False))) → (p3 ∧ p4)) → ((True ∨ True) ∧ ((p2 → False) ∨ (p4 ∨ (p5 ∨ p2)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 → p3) ∨ (True → ((p2 ∧ p1) ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621084152437134263733667365141 : (((((p3 → True) → (((p2 ∨ p1) → ((p4 ∧ True) ∨ p5)) ∨ (((p4 → p1) ∨ (p1 ∨ p5)) → ((False ∨ False) → (p3 ∧ p2))))) ∨ p3) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634720628492159963498231324691 : (((((((p1 → ((((False → p3) → (p1 → (p1 ∧ p2))) ∧ (False → (True ∧ False))) → p2)) ∨ p2) → True) ∨ ((False → False) → p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118459078680843878270799166535 : ((p3 ∨ (((p4 → (((False → True) ∧ p1) → (p2 ∧ True))) → ((p1 ∧ ((False → p5) ∨ True)) → (p2 ∨ (p2 → p1)))) ∨ p5)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617510597019250684702208151413 : ((((((p5 → (True ∨ True)) ∧ (p1 → p1)) ∧ (p3 → (((False ∨ p4) ∨ (False ∧ ((p1 → p2) → (False ∨ p1)))) ∨ (False ∨ True)))) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183745681157215705592064720298 : ((p5 → ((((p5 → True) ∧ p2) ∧ (p5 ∧ (p5 ∧ p4))) → p5)) ∧ (p4 ∨ ((((p5 ∧ (True ∧ p5)) ∨ p5) ∨ ((p5 ∨ True) ∨ True)) ∨ p4))) := by
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
  let h7 := h4.left
  let h8 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_306473444210064464665658329080 : (p1 ∨ ((True → p4) ∨ ((((((p5 ∨ p3) → p2) → p4) → (((p3 ∨ p2) → True) ∧ (p4 ∧ ((p2 ∧ p3) ∧ p3)))) ∧ (False → p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256399341860935697226024068344 : ((False ∨ p3) → ((p5 → ((((False ∨ p1) ∧ p3) → ((p4 ∧ p2) ∨ (((p1 → p4) → (False ∧ (p2 ∧ p3))) ∨ p5))) ∨ (p5 → p5))) ∨ False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112969775992101200529858553034 : (((p1 ∧ ((((p5 ∧ ((False ∧ (p5 ∧ p2)) ∧ (True ∨ False))) → p4) ∧ (((True ∨ p4) → p1) ∧ True)) ∨ (p1 ∨ True))) → p3) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64240205631583685271789380607 : ((False ∨ (p1 ∨ ((((p5 → ((p5 → p4) ∨ ((p3 → (p1 ∧ (p1 → (p1 → p1)))) → (p5 ∧ p2)))) ∧ p2) ∧ p1) ∨ (False ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675727930679604700779780755479 : (((((p5 ∧ ((p4 → (((p4 ∨ p2) → p4) → (True ∧ p2))) ∧ (p5 ∧ p3))) ∧ ((False ∧ p5) → p5)) ∧ (p5 → ((p2 → p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765052372622780455865719471474 : (((p4 ∧ (((p3 ∨ (((((p2 → p5) ∨ p3) → ((p4 ∨ (True ∧ (True ∨ p5))) → p3)) → p2) ∨ True)) ∧ (p2 ∧ p2)) ∧ (False ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



