variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768413618313916467759099646875 : (((p5 ∧ (((((p2 ∧ (p3 ∧ True)) → p4) → p3) ∧ (p2 ∧ (((p4 ∧ p2) ∧ True) ∧ (p4 ∧ p2)))) ∨ ((p4 → p2) → (p3 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_754686944101359934530819135042 : (((False ∧ (p5 ∧ (((p3 ∧ False) ∨ (True → (p2 ∨ ((((p2 ∨ (p5 ∧ (True → p5))) → (False ∧ False)) ∧ True) ∧ (False → p3))))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63108348252316053473528796894 : ((p5 ∧ ((p4 → ((p4 ∧ ((((False ∧ p1) ∧ (((p1 ∧ (p5 ∧ True)) ∨ False) ∨ False)) ∧ (True ∧ (p2 ∧ p2))) ∧ p2)) ∧ True)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135430540932515754863754884823 : (((p3 ∨ (((((p4 → (p3 ∧ p2)) ∧ True) → (p5 ∨ (True ∧ p2))) ∧ (True ∨ p2)) → p1)) ∨ ((p4 → p4) ∧ p2)) ∨ ((p2 ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111940600655497452176196606342 : ((((((p3 → ((p1 ∨ p4) ∨ p5)) ∧ (p3 ∨ p4)) → p2) → ((False ∧ p5) ∧ (p5 ∨ (((p2 → True) → p3) ∨ p2)))) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313051654893901197210630244236 : (p3 ∨ (((((False ∧ (p1 ∨ False)) ∨ p4) ∨ (p4 → (False ∨ (p2 ∧ (p2 ∧ (p3 ∧ (((p1 ∧ (p4 ∧ p1)) ∧ True) → p5))))))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723493638507303101053195981170 : (((((p5 ∧ p3) → True) ∧ (p5 → ((((p4 → p4) ∧ ((p2 → p3) ∧ (p2 → p1))) → ((True → p2) → (p1 ∨ (p3 ∧ p5)))) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40175016887807287773636224365 : (((((((p2 ∧ False) ∧ (p3 → p5)) → p2) → (p5 ∧ (p3 ∨ (p2 → (p2 ∧ (False ∧ (p3 ∧ (False → (p2 → p3))))))))) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217988242898281621071042522023 : (((p4 ∧ p2) ∧ (p4 ∧ True)) → (((((p1 ∧ ((p5 ∧ p2) → (p3 → ((False ∨ (p2 → (p5 ∨ p1))) ∧ False)))) ∧ p4) ∨ p5) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264527559357567949097493974759 : (True ∧ ((p2 → (p5 ∨ p2)) ∧ (p1 → (p2 ∨ (p4 → (((((p5 → True) → True) ∧ ((False ∧ p2) ∧ p2)) ∨ (p3 ∨ (p4 → p4))) ∨ False)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60415328994426577121699905286 : (((p4 → p1) → (((p1 → False) ∨ (((p4 ∨ p1) ∨ (p2 → False)) ∨ True)) ∨ ((((p3 ∧ ((p5 → p4) ∧ p2)) ∧ p3) ∨ False) → p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_339965812151162693046719304640 : (p1 → (p1 → (((p3 ∧ (((p2 → ((p5 ∧ ((p4 ∨ p1) → ((True → p3) ∨ p2))) ∨ p5)) ∧ ((p2 ∨ p3) ∧ p2)) ∨ p5)) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336465816046718969904146832330 : (p1 → ((p1 → ((p4 ∧ (True ∨ (p1 → p5))) → (((True → (False ∨ False)) ∧ p2) ∧ ((False ∧ p1) ∧ (False ∨ (True → (p1 → p4))))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_891854878531982333872073201374 : ((((((True ∨ (True → p1)) → ((p2 ∧ (p1 ∨ (True → ((True ∧ False) ∧ (False → (True ∨ p2)))))) ∧ p1)) ∧ p1) ∧ (p3 ∨ (p4 → p4))) → p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (True ∨ (True → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ (True → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168327948204536134026418286412 : (((p3 → p5) ∧ ((p5 ∧ ((((p1 ∨ True) ∧ p3) → False) ∧ (p5 ∧ (p2 ∨ False)))) ∧ p4)) → ((p3 ∨ p2) → ((p3 → (p4 → False)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h21 := h19.left
    let h22 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h28 =>
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233470985501132871055786965389 : ((False ∨ (p5 → p3)) → (True ∧ ((((p2 → True) ∧ (True → ((False ∨ p4) ∨ False))) ∨ p3) ∨ (False → (p1 → (((p4 ∨ p1) ∨ p1) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204308360167107868698342787719 : (((False ∧ (False ∨ (p4 ∧ p5))) ∧ p4) ∨ (((p2 → (((p4 ∨ (p2 ∧ (False ∨ p5))) ∨ p1) ∧ True)) → (p2 → True)) ∨ ((False ∧ False) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174124884122088606265406162912 : (((p3 → (((p3 ∧ (False ∨ (p2 ∧ (p4 ∧ False)))) ∧ p2) ∧ p3)) ∧ (True ∧ p3)) → (((p2 ∧ p2) ∨ ((p4 → (False → p3)) ∧ False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810664340904774572290351808419 : (((p5 → ((p1 → (p2 ∨ p5)) ∧ ((p2 ∨ (p4 → ((p5 → p5) → (p3 → p3)))) ∧ (((p2 ∨ (p4 → (p4 → p1))) → p1) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616625339108112195747937658572 : ((((((p5 → p4) ∨ (((p3 ∨ (p1 → p5)) ∨ p4) → p3)) ∧ ((p5 ∨ p2) → ((p2 ∧ p4) → ((True ∧ (p4 ∧ False)) → p1)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_148967703347873121210729286106 : ((((False ∧ p5) → p5) ∧ (((p2 ∧ ((p1 ∨ (p5 ∧ p2)) → p2)) → ((p2 → (p3 ∨ True)) ∧ p5)) ∨ True)) ∨ (p3 ∨ ((p2 ∧ True) ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117132556767698503676628311533 : (((p5 → True) → ((p3 ∧ ((p3 → ((p1 ∧ ((p3 → (p2 ∨ (False ∧ p2))) ∧ p3)) ∧ True)) → ((True ∨ p4) → p3))) ∨ p1)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106515776476671568125469659991 : ((((((p3 ∧ p5) → p4) ∧ p2) → (p4 ∧ p4)) ∨ ((p1 → ((p5 ∧ (p1 ∨ p3)) ∧ p1)) → (p1 ∨ ((True → False) → p2)))) ∧ (False → p2)) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58773702610472966368462544488 : (((p4 → p3) ∧ (((False → p5) ∧ (p4 ∧ (True ∧ True))) → (p1 ∨ (True ∧ ((p4 ∧ (((p3 → (p1 ∨ True)) → p1) ∨ False)) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82427112387880993166554659743 : ((((p4 → p5) ∨ (((((p5 ∨ True) ∨ (p5 ∧ p4)) ∧ (True ∧ (p3 ∨ False))) → p2) ∧ (True ∨ p2))) ∧ (((p2 → False) ∧ p2) ∧ True)) → False) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h15.left
      let h18 := h15.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h19 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h20 := h17 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h3.left
      let h23 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
      have h26 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h24, we can now drive its conclusion.
      let h27 := h24 h26
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338347168442487477569175461108 : (p1 → (((p5 ∨ (p5 ∨ p5)) ∧ p5) ∨ (p2 → (p5 ∨ (((p1 ∨ (p2 → p1)) ∧ (p3 ∨ p4)) → (((False ∨ p3) → p5) ∨ (p3 ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118564796214780787282259630586 : ((p4 ∨ ((((p3 ∧ p4) ∧ (p1 ∨ ((p2 ∨ (False ∧ (p3 → ((p5 ∧ p4) ∨ False)))) → p5))) → ((p1 ∧ p3) → p5)) ∧ p1)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118760404429097713808585256137 : ((p5 ∨ ((True ∧ p2) → ((p2 ∧ ((True → p2) ∧ (((p3 ∧ (p4 ∨ (p1 ∨ p4))) → p2) ∧ (p3 ∨ False)))) → (p4 ∧ p5)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634159458115017315409210840544 : ((((((p4 ∧ p3) ∧ ((True ∨ ((False ∧ ((True ∨ (p2 ∨ (p1 → ((p2 ∨ False) ∧ p3)))) ∧ False)) ∧ False)) ∧ p2)) → (p2 ∧ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262374583458133665164415533603 : (True ∧ (((True ∨ p1) ∧ (p2 ∨ (p4 → (p5 → ((((p1 → (True ∨ (p1 ∨ p2))) ∧ (True → p1)) ∨ False) ∧ ((p1 ∨ p5) ∧ False)))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37627460804515486632953034117 : ((((((p3 → (((((False ∨ p1) → (p1 ∧ (p1 ∨ (True ∧ True)))) → p5) ∧ (p2 ∨ p5)) ∨ (p3 ∨ False))) ∨ False) ∨ p3) → p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708332703189833594316062046498 : ((((((p4 → ((False → p4) → True)) ∨ p5) ∧ p5) → (False ∧ (False ∧ (p3 ∧ (p4 ∨ ((True ∨ (p1 ∨ (p2 ∨ (p3 ∨ p1)))) ∨ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2360565667566437377880715725 : (((False ∧ (p3 ∧ (p3 → ((p1 ∧ (True ∨ p4)) ∨ False)))) ∧ p4) ∨ ((True ∨ ((p1 ∨ (p1 ∧ (p5 ∧ p2))) ∧ (p1 ∨ p5))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266178844744093474257603298527 : (True ∧ (p4 → ((((((False ∧ (((p5 → ((True ∨ False) ∧ p1)) ∨ ((p4 ∨ (p5 → p4)) ∧ True)) → False)) ∧ p3) ∨ p4) ∧ False) ∧ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192670700952755353532524829761 : ((((p2 ∧ (p2 ∨ (p1 → (p2 → False)))) → p1) → p1) → ((p3 ∨ ((p3 ∧ True) ∧ (p3 ∨ (p2 ∧ (p3 → (p1 ∨ False)))))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158393510959899800760891082440 : (((p3 → p3) ∧ (((((((p1 ∨ p1) ∧ p2) → (p5 ∧ False)) → (p4 → False)) ∨ p3) ∧ False) ∧ p2)) ∨ ((((False ∧ p2) → p1) ∨ p1) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171686316223708293499300978366 : (((p4 ∨ (((p5 ∨ True) ∧ (((p5 ∧ True) → True) → p4)) ∧ (True ∧ True))) ∨ True) ∨ (((True → (p3 ∨ ((p4 → p2) → False))) ∨ True) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251650399404298823539635762339 : ((p3 → p1) ∨ (p4 → (p3 → (((p1 → (p5 ∨ (p3 ∧ (False ∧ (((p2 ∧ p4) ∨ False) ∧ (p5 ∨ p4)))))) ∧ p2) ∨ (True ∧ (p5 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199386017710340583204046790445 : ((((True ∧ (p2 ∨ True)) → (p1 ∨ p1)) ∨ False) → (((p1 ∨ (False → p3)) ∧ p3) ∨ (p1 ∧ ((p2 ∨ p3) ∨ ((True ∧ (False ∧ p2)) → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (True ∧ (p2 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732281932078773550885987091796 : ((((False ∧ False) ∧ (((p2 ∧ (p2 → False)) ∧ (((False → p5) → p5) ∧ (((p3 ∨ p1) ∧ (((False ∨ p4) → p1) ∨ p5)) ∧ True))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347329150977467925649740453576 : (p3 → ((True → (p3 → (False ∨ ((True → False) → (True → p1))))) → (((p3 → ((False ∧ p3) → (p1 ∧ p5))) ∧ (p1 → (p2 ∨ p2))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312573735065792264975567217547 : (p3 ∨ ((((((((False ∧ (p4 → p4)) → p4) ∨ True) → p2) ∨ (p5 → (p3 → (p3 ∨ ((p2 ∨ p3) ∨ (p5 ∨ p1)))))) → p5) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_211436549305419124864537896096 : (((p5 → True) ∨ (True ∧ p5)) ∧ (((p2 → ((p5 ∨ p5) ∨ (p4 → p5))) ∨ (((p5 → (p3 ∨ (p2 → True))) → p5) ∨ (p1 → True))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698099077768437371759906663686 : (((((False ∨ ((p3 ∧ (False → True)) ∨ (p2 ∧ (False ∨ p2)))) ∨ True) ∨ (((((p2 ∨ p1) ∧ True) → ((p4 → p2) ∨ p2)) → p5) → p2)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_112568649741942403680897697114 : ((((p1 ∨ ((p1 ∨ (p5 ∧ False)) ∧ ((((False ∨ ((p4 ∨ p1) ∧ False)) ∧ False) ∧ (p1 → (p4 → p5))) ∨ True))) → False) → p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35095585481601057765426676035 : ((p1 → ((((((True ∧ ((False ∧ p5) ∨ p1)) → (p4 → (False ∧ p1))) ∨ (p4 → False)) ∨ True) → p5) ∨ ((True ∧ p3) → (p5 ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48170955362799234056300377884 : ((((True → False) ∧ (p5 → ((p4 → (p2 ∨ False)) ∨ (p4 ∧ (((p2 ∧ (p1 ∧ p1)) ∨ (p2 ∨ (p2 ∧ p5))) ∨ p1))))) → (p2 ∧ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774043325530173719807343021325 : (((False ∨ (((((p4 ∨ p2) ∧ (True → ((p4 ∧ (True ∧ (p2 ∨ (False ∧ False)))) → True))) ∨ ((p4 ∨ False) ∧ p1)) ∨ True) ∨ (p2 ∧ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691195750082780677177345610001 : ((((((False ∧ p1) → ((True ∧ False) ∨ False)) ∨ (False ∧ (p3 ∧ ((p2 ∨ p4) ∨ p3)))) → ((p2 ∨ (((p4 → p4) ∨ p1) → p4)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230737660507417813677417994872 : (((p5 → p2) ∧ p3) → (((p1 ∧ ((p3 → ((p4 ∨ ((True ∨ False) → p1)) ∨ ((p2 ∧ p4) ∨ (p3 ∧ p2)))) ∨ (False → p4))) → p4) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244251202946145294401847917341 : ((False ∧ True) ∨ ((((p2 ∨ p2) ∨ False) ∧ ((p4 ∨ ((((False ∨ (((True → True) ∧ (p2 ∨ False)) ∧ True)) ∧ p1) → p1) ∧ p5)) ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649727677634721830003730104402 : ((((((False ∨ ((False ∨ (((((p4 ∧ (p2 → False)) ∨ p2) ∧ p2) → (p1 ∨ p1)) → p4)) → p2)) ∨ p1) → (False ∧ p2)) ∧ (p3 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325057998001991470588144187284 : (p5 ∨ ((p2 ∨ False) → ((((((p5 ∧ (p4 ∧ (((False ∧ False) ∨ False) → False))) ∧ False) ∨ (p2 → ((p1 ∨ False) ∧ True))) ∧ True) ∨ p2) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68462421737126269986245971462 : ((p3 → (p3 ∧ ((p2 ∨ (p1 ∨ ((False ∧ p5) ∨ (((p2 → (((True → True) → ((False ∧ False) ∧ p3)) ∧ p2)) ∨ False) ∧ p1)))) ∨ p3))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_187083173250759102465422509191 : (((False → p4) ∧ (p4 ∧ ((p5 → p2) → ((False ∧ True) ∨ p3)))) → ((p4 → (p2 ∨ (p2 ∨ (True ∨ (p5 ∧ (p5 ∧ (False ∨ False))))))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303154464580706759313818543246 : (False ∨ (p3 → (p2 → ((((p4 ∨ ((False ∧ (((False ∧ ((p3 ∧ p3) ∧ p5)) ∧ p4) → ((p1 ∨ False) ∧ p2))) ∧ p4)) ∨ p5) ∨ p2) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56086061608733957248401534885 : ((((p3 → (p4 → True)) → False) ∨ (p2 ∨ ((p2 → (((p3 → p2) → (True ∧ p3)) ∧ p3)) → (False → (p4 ∨ (p4 → (p4 ∨ p1))))))) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158660393253471983772579656386 : ((p1 ∧ (p2 ∨ (((((p5 ∨ True) ∨ p5) → (p3 ∨ True)) ∧ ((True ∨ p3) ∧ p2)) → (p5 ∨ p4)))) ∨ ((p5 ∨ p4) ∨ (p5 → (p4 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233542009409616520010216962740 : ((p1 ∨ (p4 ∨ p1)) → ((((p4 ∧ p2) ∨ ((p5 ∧ False) → (p4 ∨ True))) ∨ (p3 ∨ (p2 ∧ ((p3 → ((p3 ∨ True) ∨ p4)) ∧ p1)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265823081867890542010362806992 : (True ∧ (p5 ∨ ((((p1 ∧ p3) → (((True ∧ True) ∧ p2) → p1)) → ((p4 ∨ ((True ∧ ((p5 → p5) ∧ True)) ∨ (p4 → p5))) ∧ False)) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ p3) → (((True ∧ True) ∧ p2) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135803976492635423151842592479 : (((p1 ∨ (((p4 ∨ (p1 ∧ p5)) ∨ p5) ∧ ((p3 → (p2 ∨ True)) → p2))) → ((p3 ∨ (p4 ∧ (p4 → p4))) ∨ p1)) ∨ (False → (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187861169837823814462131235598 : ((p5 → (p1 → (((True ∧ ((True ∧ p1) ∧ p3)) ∨ True) ∨ False))) → ((p3 ∨ ((p4 ∧ (p3 ∨ False)) ∨ (p4 ∨ (p3 → (p5 → p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_857021061756926651537659049014 : (((((False ∨ (p5 ∨ (((True ∧ (p4 → (True → ((p3 ∧ p5) ∨ (True ∨ p3))))) → p1) → (((True ∨ p1) ∨ p5) ∧ p1)))) ∨ p4) → False) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ (p5 ∨ (((True ∧ (p4 → (True → ((p3 ∧ p5) ∨ (True ∨ p3))))) → p1) → (((True ∨ p1) ∨ p5) ∧ p1)))) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∧ (p4 → (True → ((p3 ∧ p5) ∨ (True ∨ p3))))) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32256944798401012138390048198 : ((p1 ∨ (True ∧ (p1 → ((False ∧ (p5 ∧ p1)) ∨ ((p3 ∧ p4) ∨ (p1 ∨ ((p2 ∧ ((p3 → True) ∨ p4)) ∨ ((True ∧ p5) ∧ p5)))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136266682454271802256424507529 : ((((False ∨ (p2 ∨ (p3 → p3))) ∨ p3) → ((((p1 ∧ (p4 ∨ p5)) → (p1 → (p4 ∧ p4))) → (False ∧ p3)) → p4)) ∨ (True → (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198881445793447909427081337209 : ((p2 → (p3 ∨ ((p5 ∨ p3) ∧ (p5 ∨ p1)))) ∨ ((p5 → p2) ∨ (p5 → (p3 → (((((p2 → p2) ∧ p3) ∨ (p1 ∨ p1)) ∨ False) ∧ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217366692478067725691393818510 : (((p4 ∨ (False ∧ p1)) ∨ p5) → ((((p3 ∧ p2) ∧ False) ∨ (((False ∨ True) ∨ (False → p2)) → (True ∧ ((p3 ∧ True) → True)))) ∨ (p2 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722899417157824523351683714094 : (((((p3 ∧ p2) ∨ p1) ∧ (p2 ∧ (((False → ((p1 ∨ (p4 ∧ p5)) ∧ (p5 ∧ (p1 ∨ p3)))) → (p3 → (p5 ∨ (p1 ∨ p4)))) ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342564440146450250077562801466 : (p2 → ((((((p5 → p2) → p5) → (False ∨ False)) ∨ (p3 ∧ p2)) ∨ p5) ∨ (((((True → False) ∨ p4) ∧ (p4 ∧ (True → False))) → p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358605676441563446484821151213 : (p5 → (p3 → (((p5 ∧ (p2 → (p3 → (p5 ∨ p5)))) → p2) ∨ (p2 ∨ (True ∧ ((p5 → (p2 ∧ p1)) ∨ (((p3 → p3) → p3) → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324586575521794572916697371791 : (p5 ∨ (((p2 → p3) ∨ True) ∧ ((((p2 ∨ True) ∧ (p1 → p4)) ∧ p2) ∨ (False ∨ (p1 → (p3 → (p1 ∧ ((p4 ∧ p4) → (p3 → p4))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752112495736574929233151745052 : (((True ∧ (p1 → ((p2 ∧ (((True ∧ ((p5 ∧ (p4 → (p1 → True))) ∨ (((False ∧ p4) ∨ p2) ∨ p1))) ∨ p2) ∧ (True ∧ True))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319886858860030858083281711686 : (p4 ∨ ((p2 ∨ ((p4 ∨ p3) ∧ p3)) ∨ (((p2 ∨ p5) → p3) ∨ (p1 → (((True ∧ p5) ∧ p4) → ((p1 ∧ ((p5 → p3) ∧ False)) ∨ p1)))))) := by
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
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113015910171449735784090946819 : (((p5 ∧ ((True ∨ ((p3 ∨ p4) ∨ (p1 ∧ (True ∨ p1)))) ∧ ((p5 ∨ (((p1 ∧ p1) → True) ∨ p4)) → (p5 ∨ False)))) → p3) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800775824654273054653652694605 : (((p2 → (((((p4 ∨ (p4 ∧ (p5 ∨ p4))) → (p4 ∨ p1)) ∨ p3) → (((p1 ∨ p1) → (p1 → (False ∨ p1))) → p4)) ∧ (p3 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642134317644229263861731943625 : ((((True ∧ ((True ∧ (((p3 ∧ p3) ∧ True) → (p3 ∨ p2))) ∨ (((p3 ∨ (p5 ∧ True)) ∧ (p3 ∨ p5)) ∨ (True → (p5 ∨ p1))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43633653037810909505579323533 : (((((((True ∧ (((p5 → ((True ∧ p5) ∧ (p1 → False))) → p3) ∧ (p1 ∧ (p3 ∧ p1)))) ∧ False) ∨ True) ∨ (p1 ∧ p2)) → p5) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216764419270875651823781003824 : ((((p4 → False) → p4) ∧ p5) → (((p3 ∨ p5) → (((p4 ∨ (p1 ∧ False)) → (p1 ∧ ((p4 → p3) ∧ p1))) ∧ (p2 ∧ p2))) → (p4 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ (p1 ∧ False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_986541978342800954830675455235 : (((p2 ∧ (((True ∧ (p3 ∧ p5)) ∨ True) → (((p2 → p2) ∧ (((p4 → p3) ∨ p4) ∨ ((p5 ∧ p3) → True))) ∧ ((p1 → True) ∧ False)))) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∧ (p3 ∧ p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681253878830386397439531047525 : ((((p4 ∧ (p1 → ((((p2 ∨ ((p3 ∧ (True ∨ p3)) → p4)) ∧ p3) → (p3 ∧ p5)) ∧ (True ∧ False)))) → (((False ∨ p2) ∧ p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347756721641046675275923417680 : (p3 → (((p2 → False) ∧ p2) ∨ ((p4 ∨ (p1 ∨ ((((p2 → p5) ∧ (p2 ∧ p5)) ∧ ((p5 ∨ ((p5 ∧ p4) ∧ p4)) → p1)) ∨ p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214530423906243785900432234894 : (((p5 ∧ p4) ∧ (False ∧ p1)) ∨ (((False → (((p2 ∧ p3) ∨ False) ∧ p4)) ∨ (p4 ∧ ((p5 → (p2 ∨ False)) ∨ p1))) ∧ (True → (p5 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112334778839268052293337818738 : (((p4 → ((p3 ∨ p5) → ((p2 ∧ ((p3 ∨ (p4 ∧ (p2 ∧ (p3 ∨ True)))) → (False ∧ (True ∨ (True ∨ p5))))) ∨ p2))) ∨ p1) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53115027257249202629815867366 : (((p2 → (p2 → (((p2 ∧ ((p1 ∨ p5) → p2)) ∨ p2) → False))) ∧ ((p4 ∧ p2) ∨ (p2 → ((False ∧ True) → ((False ∨ p1) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355630809208034840928499733287 : (p5 → ((p4 ∨ ((((p3 ∧ True) → False) ∧ p5) → ((p1 ∧ (True ∧ (p5 → p4))) → ((p3 ∧ ((True → p5) ∧ p5)) ∨ p4)))) ∨ (p3 ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h11 := h7 h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119911620620780910337886114109 : ((((((True → False) ∧ p2) → ((((((p2 → p3) ∧ False) → p1) ∨ True) ∨ p2) ∧ ((p4 ∨ p4) ∨ p5))) → (False ∧ p1)) ∧ True) → (False ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((True → False) ∧ p2) → ((((((p2 → p3) ∧ False) → p1) ∨ True) ∨ p2) ∧ ((p4 ∨ p4) ∨ p5))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h4
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133737157785028663367674369603 : ((((p3 → (p2 ∧ (((p2 ∧ (p4 ∧ p5)) → p5) ∨ p4))) ∨ ((p2 ∨ (False ∨ p1)) ∨ ((True → p2) ∨ p5))) ∧ True) ∨ (p3 ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62194401313717573357060642304 : ((p3 ∧ (((p2 ∨ (((((p4 → p1) → p5) → p2) ∧ (p2 ∧ (((p2 → (True ∨ p2)) ∨ p5) → p2))) ∧ p4)) → (True ∧ p3)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148683034986470064047111311729 : ((((p1 ∧ (p4 ∧ p5)) ∨ (p3 ∨ (p2 ∧ False))) ∨ (((p2 ∧ p4) ∧ (p3 ∨ True)) ∨ ((p4 → False) ∨ p3))) ∨ ((p2 → (p5 ∨ p2)) ∨ p1)) := by
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
theorem thm_5_vars_215756303796218759370748127316 : ((p1 ∨ ((p4 → p5) ∧ p5)) ∨ (((p4 ∨ ((p5 ∨ p1) ∧ ((((False → (p2 → p1)) ∧ (p3 → (p1 ∧ True))) ∧ p4) → False))) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190524759217026627332904010615 : (((((p5 ∧ p2) ∨ ((p3 ∧ p1) ∧ p2)) → False) → p3) ∨ ((p5 → ((((p1 → p4) ∨ p2) ∨ ((p3 ∨ p5) ∨ p4)) ∨ (p5 → p1))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111791401816790403525824277253 : ((((True ∧ (((p1 ∧ p4) ∧ ((False → p5) ∨ ((p3 ∧ True) ∨ p2))) ∨ ((p1 ∧ (p1 → True)) ∨ False))) ∨ (True ∧ p3)) ∨ p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164739486695388290274018714180 : ((((p1 ∧ ((False → p1) → (p1 → ((p2 ∧ p1) → (p2 → False))))) ∧ (p1 ∧ p1)) ∨ True) ∨ ((((False ∨ p1) → p4) → False) ∨ (p3 ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322595435801877046771551622824 : (p5 ∨ ((p1 → ((p3 ∨ (((((p2 ∨ p5) ∧ False) → (False ∨ p5)) ∧ (False → True)) → (p5 ∧ (p1 ∧ p1)))) ∧ ((p3 ∧ p3) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192936444355571697450900787709 : (((((p2 → p1) ∧ p1) ∨ (True ∧ p5)) ∨ (p5 ∧ True)) → ((((p2 ∨ False) ∨ (p1 ∨ ((p3 ∨ p3) → (p1 ∧ p4)))) ∧ (p4 ∧ True)) → p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h7
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- One of the premise coincides with the conclusion.
          exact h22
      case inr h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h4.left
      let h36 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h41 =>
          -- Conjunctions on the left can always be decomposed.
          let h42 := h41.left
          let h43 := h41.right
          -- One of the premise coincides with the conclusion.
          exact h35
      case inr h44 =>
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- One of the premise coincides with the conclusion.
        exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51566401636310268881974364648 : (((p1 ∨ ((False ∨ (p5 → (False ∨ True))) ∨ (p1 ∧ ((p4 → p2) ∧ ((p2 ∨ p5) ∨ p5))))) → ((p2 → ((True ∨ p3) ∧ p4)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654239625180271756384467660896 : (((((((p5 ∨ p5) → ((p2 → (p2 → ((True ∧ ((p3 → False) ∨ (True ∨ True))) ∨ (p3 ∧ p2)))) ∨ p3)) → p3) ∨ p5) ∨ (False → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192714958093508390401353301597 : (((((p2 ∧ p3) → p3) ∨ ((True ∨ p4) ∨ False)) → p3) → (((True → ((p2 ∨ p2) ∨ (p5 ∨ ((p4 ∧ (p3 ∨ p2)) ∧ True)))) → p5) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ p3) → p3) ∨ ((True ∨ p4) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167174362504189955902117984846 : ((((False → False) ∨ ((p4 ∧ (p4 → p4)) ∨ (False ∧ (p3 ∨ ((p2 → p3) → p1))))) ∨ p5) → ((p5 ∧ False) ∨ ((p1 ∨ False) → (False → p5)))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213096755272762547251416027887 : ((((True ∨ p5) ∧ p2) ∧ p1) ∨ ((((True ∧ (p4 ∨ True)) → False) ∧ p3) ∨ (((p1 → p5) ∧ False) ∨ ((p1 ∧ ((p4 ∨ False) → True)) → True)))) := by
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



