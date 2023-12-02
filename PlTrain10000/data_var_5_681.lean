variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132132462901368405782803460488 : ((True ∧ ((p4 ∧ (p2 → (((True → p2) → (p3 ∧ (p4 ∨ p5))) ∨ (((p1 ∧ p4) ∨ (p2 ∧ p5)) → p4)))) ∨ True)) ∧ ((p1 ∨ p5) ∨ True)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159312984898389933718795818555 : ((p5 → ((p1 ∨ (p2 ∧ ((p5 → True) ∧ (p2 ∨ (p3 ∨ ((p5 ∨ p3) ∧ p1)))))) ∧ (p1 ∨ p4))) ∨ (p4 ∨ ((True ∨ True) ∨ (p1 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747484610963487084575193842277 : ((((True → p1) → (((p1 → ((True ∧ (p2 → ((p1 → (((False → (p1 ∨ p5)) ∧ False) ∨ p3)) ∧ True))) ∨ p4)) ∨ p3) ∧ (p4 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184370277721862312480471405838 : (((p4 ∨ ((p5 ∧ ((p4 ∨ p5) ∧ (p1 → p5))) → False)) → p1) ∨ (p1 ∨ ((p1 ∧ (False → ((p3 ∨ ((p5 → False) ∨ False)) → p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705010638381813561115183509189 : ((((p1 → (((p4 → p2) ∨ p3) → (p1 ∨ (p2 → p3)))) → ((p1 ∧ ((False ∨ (p1 ∨ p1)) → p3)) ∨ (p3 ∨ ((p5 ∧ p1) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326975149416545322419342439306 : (True → (((False ∧ (p5 ∧ (((False → p5) → ((p1 → (p4 ∨ p2)) → p5)) → ((p4 → False) → (False ∨ p3))))) ∧ ((p4 → True) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315467256957382469952558025645 : (p3 ∨ (((True ∨ True) ∨ p5) → (True → (((p2 → (False ∨ p1)) → p3) ∨ ((p4 → ((p1 → (p1 ∨ False)) ∨ p3)) ∨ ((p2 ∨ p3) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717909247469450523552058808584 : (((((p4 ∨ (p3 ∨ p3)) ∧ False) ∨ (((p5 ∧ (((p4 ∨ ((p5 ∧ False) → False)) → p3) → p4)) ∨ (True → ((p4 ∧ True) → p4))) ∨ False)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262155644834013361223217836948 : (True ∧ ((((((p3 ∧ p1) ∨ (p1 ∨ ((p5 ∨ False) ∨ p1))) ∧ False) ∨ (p2 ∨ (False → ((((p1 → p3) ∧ p5) ∨ p3) → p2)))) ∨ p1) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66142512549186015431435226588 : ((p5 ∨ (((p5 → (False → p4)) → ((p4 ∨ (True → p3)) ∧ (((p1 → (False ∧ ((p1 → p1) ∧ p4))) ∧ p2) → True))) ∨ (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127732018939038699889040483233 : ((True → ((p1 ∧ ((p1 ∨ (p5 ∨ (p5 ∧ ((p2 ∧ (p4 ∧ ((False → p1) ∨ ((p1 → p4) ∨ p3)))) ∧ p1)))) → p1)) ∧ p2)) → (p2 ∧ p2)) := by
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153157161173702679615190690128 : ((p5 ∧ ((((p3 → False) ∨ (((p5 → (p3 ∧ p2)) ∨ ((p5 ∨ p1) → p2)) ∧ p2)) → p1) ∧ (True → p1))) → (((p1 ∧ p5) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313359161078456827344790061324 : (p3 ∨ ((p3 → (((p3 ∨ ((((p1 → ((p1 ∧ p2) ∨ p4)) → p2) ∨ ((True ∨ p2) → ((p1 ∧ p2) ∧ p5))) ∨ True)) → p2) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147441516084993759105180786875 : ((((p1 → p2) ∧ (((p4 ∧ (((True → (p5 ∨ p5)) ∧ (p5 ∧ (p4 ∨ p1))) ∧ p3)) → False) ∧ True)) ∨ p3) ∨ ((False → p2) ∨ (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164992613400035464394804360537 : (((((p1 ∧ p3) ∨ ((p3 → p4) ∧ ((p1 ∧ p5) ∨ p5))) → ((p3 ∧ p1) ∨ p4)) → p1) ∨ (((False → (p2 ∧ False)) ∧ False) → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249216392903605554804865809664 : ((p4 ∨ p3) ∨ (p5 ∨ (p3 → (((((p4 ∨ (p2 → (p4 → (p3 ∨ p2)))) ∧ False) ∨ True) ∨ p1) ∧ ((p4 → (True ∨ p4)) ∨ (p2 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117383405779514841052696036420 : ((p1 ∧ (((True ∧ ((True ∨ ((True ∨ False) ∨ ((True → p4) ∨ (((p4 → p3) ∨ False) ∧ False)))) → True)) → (True ∧ p3)) ∧ True)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143037335227778160609863191892 : ((False → ((p4 ∧ (p4 → ((((p5 → False) → ((False → ((p1 → (p5 ∨ p5)) → p2)) ∧ p4)) ∨ False) ∧ p3))) ∧ True)) → ((p3 ∧ p1) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314016873793017763744997777510 : (p3 ∨ ((False ∨ ((p3 → (p4 ∧ (((False → p1) ∨ ((p2 ∨ (p2 ∨ True)) ∨ p2)) → p3))) → ((p5 → (p3 ∧ p5)) ∨ p2))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233608178657633990698788273267 : ((p2 ∨ (p2 ∧ True)) → ((((p5 ∨ ((p4 ∨ p4) → p3)) ∨ p2) ∨ p1) ∧ (p1 ∨ ((((p2 → True) → (p1 ∨ p3)) ∨ (False → p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111276993691385069263034326209 : ((((True ∨ p2) → (((True ∧ p1) ∧ p5) ∧ (((((p1 ∧ p4) ∨ p4) ∨ (p1 ∧ ((p4 → p2) ∨ p3))) ∨ p3) ∧ p3))) ∧ p3) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233940841825335496271914851115 : ((p4 ∨ (p5 → False)) → (((p3 ∨ True) → False) → (((p5 ∧ (((False ∧ (True ∨ p2)) ∧ (p3 → p4)) → True)) → p5) ∧ ((p4 ∨ True) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664091661269886694960468886134 : ((((True ∨ (((p1 ∧ (True → (p3 → ((p3 ∨ True) → p5)))) → p4) ∨ (p2 ∧ ((p1 → ((True ∧ False) ∨ p4)) ∨ p5)))) → (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56228988587678199352174985422 : (((p4 ∨ ((p3 ∨ p5) ∧ p3)) ∨ (p4 ∨ (((p5 → p5) ∧ ((((p4 ∨ p1) → p3) → (p3 ∧ p4)) ∨ (p5 ∧ (False ∧ p4)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352759345487645190385193776255 : (p4 → ((p2 ∧ p3) → (((((p3 ∨ p2) → ((((True → False) ∨ (p1 → (False → p2))) ∧ (True ∨ p4)) ∨ p3)) ∧ p5) ∨ (p1 ∧ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670633221320055055178292533427 : (((((p4 ∧ True) → (p3 ∨ (((True ∨ (((p4 ∧ (p1 ∨ p2)) ∧ p1) ∨ p2)) ∧ p3) → (p2 ∨ (True → p2))))) ∨ ((True ∨ False) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262194631142264457967001663061 : (True ∧ ((((p2 ∨ ((p2 ∨ p5) ∨ ((p5 ∧ (p3 ∧ True)) ∧ (p5 ∧ p3)))) → (p2 → ((p2 ∨ (p4 ∧ p3)) ∧ (p3 ∧ True)))) → p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691274624961399229897912270540 : (((((((p1 ∧ p3) ∧ p4) ∨ p5) → (p1 → ((False ∨ p2) ∧ ((p5 ∨ False) ∧ True)))) → ((True ∧ (p4 ∨ (p3 ∨ (p1 ∧ True)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648231425457631281012019216146 : (((((p1 ∨ ((((False ∨ ((p4 ∧ (p5 → p5)) ∧ p4)) ∨ (p5 ∧ (True ∧ p4))) ∨ p1) ∨ (True ∧ (p3 → p1)))) ∧ p5) ∧ (p3 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252804991723523263266767200836 : ((True ∧ True) → (p5 → (p3 ∨ (((((((((p3 ∧ (p2 ∨ p2)) ∨ p4) ∨ False) → p2) ∧ p3) ∧ False) ∧ p5) ∧ p1) ∨ (p3 ∨ (p5 → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213589443113914687001676357045 : ((((p1 → True) ∧ False) ∨ p4) ∨ ((((p4 ∨ False) ∧ ((((p3 ∧ (p1 ∨ p4)) ∨ (p3 ∨ p5)) → p5) ∨ (p3 → (False ∧ p3)))) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231107117430700789156200046361 : (((False ∨ p5) ∨ p1) → ((((p4 → ((p5 ∨ p1) ∨ p4)) ∧ ((p2 ∧ p4) ∨ (True ∨ (False ∧ p3)))) ∨ ((p5 → (p3 ∧ p4)) ∧ p3)) ∧ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116591312584863920947556640387 : (((p4 ∨ p5) ∧ (((p1 ∧ True) → ((p1 → (p5 ∧ (False → (False → (p2 ∨ (p1 → p2)))))) ∨ p2)) → ((p5 ∨ p5) ∨ p4))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167467177081391577605182172069 : (((p2 → (p1 → ((True ∨ False) → (p4 ∨ (((False ∧ p2) ∨ (p1 → True)) ∧ p2))))) → p4) → ((p1 ∨ False) → (p4 ∨ ((False → True) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → (p1 → ((True ∨ False) → (p4 ∨ (((False ∧ p2) ∨ (p1 → True)) ∧ p2))))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40872821250935746765174397005 : ((((((((p3 ∧ ((((p4 → p4) → (p1 → False)) ∧ p4) ∨ p3)) ∨ True) ∨ p4) ∨ (p4 ∧ p1)) ∨ (True ∨ p4)) ∧ (False → p1)) ∨ False) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325656265087339964003432405194 : (p5 ∨ (False ∨ (p1 ∨ ((p1 ∧ (False → (p1 ∨ ((p1 ∨ (p2 ∧ (True ∧ p5))) → (p5 ∧ p2))))) → (((p1 → p2) ∨ True) ∧ (p5 ∨ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117547668788614594320278307875 : ((p2 ∧ ((False ∨ ((((p5 ∧ p5) → (True → p4)) → True) ∧ (((p2 ∧ p1) ∧ False) ∨ p2))) ∨ ((p2 ∨ (p5 ∧ p4)) ∧ p4))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135504563435812070203236057433 : (((p2 ∨ ((p2 ∨ ((p4 → p4) ∨ (p2 ∧ True))) → (((p3 ∨ p3) ∧ (False ∧ True)) ∨ False))) → (False ∨ (p3 ∨ False))) ∨ ((p1 ∧ False) → p5)) := by
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
theorem thm_5_vars_317867510419269562026970824822 : (p4 ∨ (((p2 → p3) ∨ ((p3 ∧ ((p3 → (((p5 → ((p4 ∧ False) ∧ p1)) → p3) ∨ (p1 → p3))) → (p4 → (p3 → p5)))) ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669681332881389720263333456544 : ((((((False → (p3 ∨ (True ∧ p1))) → (((True → p3) → p1) → (p2 ∨ (p1 ∨ p3)))) → ((p3 ∧ p1) ∧ False)) ∨ ((True ∨ p4) ∨ p4)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115009777839215174834082520750 : ((((p4 → True) ∧ (p4 ∧ ((p3 ∨ True) ∧ (p5 → (False ∨ p2))))) ∧ (((p5 ∧ (p5 → ((True → p1) ∧ False))) ∧ False) ∧ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47210713476165177758654411085 : (((((((False ∧ (False ∧ (True ∧ p4))) → True) → p5) ∨ p1) ∨ ((p3 ∧ (p3 ∨ (False ∨ (p3 ∧ p1)))) ∨ (p3 → True))) ∨ (False ∧ p1)) ∨ p4) := by
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
theorem thm_5_vars_262399532076909893657908480725 : (True ∧ (((p4 ∨ p5) → (((False ∨ p5) ∨ p3) → (True → (p4 ∨ ((p4 ∨ (p1 ∧ ((p1 ∧ False) ∧ ((p4 → False) ∧ p5)))) ∨ p2))))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47172179409607895633825575055 : (((((p1 ∨ (((False ∧ p5) ∨ False) ∨ p4)) → ((p1 → p5) ∨ (p1 ∨ False))) ∨ (False ∨ (((p4 ∧ p1) ∨ p2) ∧ p5))) ∨ (True → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192188292824284061370757876905 : (((((False ∧ p3) → (True ∨ (False → p1))) ∨ p1) ∧ p4) → (((p2 → p4) → p2) ∨ (p4 ∧ (True → ((False ∨ (p3 → (p2 → True))) ∨ True))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601092148605487722721996722292 : ((((p1 ∧ (p2 ∧ (True ∧ ((((True ∧ ((((p3 ∧ p5) → p1) → True) ∨ p2)) → p1) ∨ ((p4 ∧ p3) ∨ p2)) ∧ (p4 ∨ True))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_91112268660296489874407559674 : (((p4 → True) ∧ ((p1 ∨ ((p3 ∨ (p4 → p4)) ∨ ((True ∨ False) ∨ p5))) → (((p5 → (p2 ∧ False)) ∧ (p2 ∧ (p4 ∧ p3))) ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p3 ∨ (p4 → p4)) ∨ ((True ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151522051201255266870807865774 : (((p5 ∧ (((p3 ∨ p2) ∨ p5) → ((((p5 → p1) → p3) → ((p5 ∧ p1) ∧ False)) → p5))) ∨ (True ∨ True)) → (((p4 → p1) → p2) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688210438927902803252882691086 : (((((p3 ∧ p4) ∧ (((p4 ∧ (False → (p1 ∧ (p2 ∨ p5)))) ∧ p3) → (p2 ∧ p2))) ∧ ((p3 → ((True → False) ∨ p4)) ∧ (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148054581885542759299720377139 : (((p1 ∨ (p5 ∨ (False ∨ ((p5 ∧ ((False ∨ (p1 → ((p4 ∨ p5) ∨ False))) → p2)) ∨ p2)))) ∨ (p2 → True)) ∨ ((p5 → (True → p2)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116418255367876552548169750784 : (((p3 ∨ (p1 ∧ p5)) → ((p4 → ((((p5 ∧ (p1 ∧ p1)) → (p3 ∨ (p3 ∨ p3))) ∧ p1) ∧ (False ∧ p4))) ∧ (p1 → p1))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683868420586267356775212442950 : (((((p4 ∧ ((((((True ∧ (p4 ∨ p5)) ∨ (p5 ∧ True)) ∨ p2) ∧ p3) ∨ p1) ∧ p4)) ∨ False) ∨ ((True ∧ False) → (p4 ∧ (p2 ∨ p4)))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936924094610212133044894493310 : ((((((p5 ∧ (p4 ∧ False)) → False) → p4) ∧ (True ∧ (p5 → (p2 ∨ (p5 → ((p4 ∨ p3) → (((p4 ∧ (p1 ∧ p5)) → True) → False))))))) → p4) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∧ (p4 ∧ False)) → False) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135449445690423854959187017359 : ((((((False → (p2 → ((p5 ∧ (p1 ∨ ((True → False) → False))) → p1))) → p2) → False) ∨ True) → ((p2 ∨ True) → p5)) ∨ ((p4 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48405633078068759609611444439 : (((p1 → ((p2 ∨ p2) → (p3 ∧ (((p4 ∨ ((p3 ∨ ((p3 → p4) → ((True ∨ False) ∧ True))) ∨ p5)) → p5) ∧ p1)))) → (False ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64542449050856047517207913283 : ((p1 ∨ (((False → (p1 → p2)) → (p3 ∧ p3)) ∨ (p5 → (p5 ∨ (p5 → ((False → True) → (p2 → (((p3 ∧ p1) → True) ∧ True)))))))) ∨ p2) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706996828625779597059554405901 : (((((False ∧ (p1 → ((p3 → False) ∧ False))) ∨ p1) ∨ ((((p5 → (False ∨ (p2 ∧ p1))) ∧ p4) ∧ ((p5 ∧ p2) ∧ (p5 → False))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_197014703974863792528292612668 : (((((False ∧ p3) ∨ p5) ∨ (p1 ∧ p4)) ∨ p3) ∨ (((((((p1 ∧ ((p3 → p5) ∧ True)) → True) → p3) ∧ p2) → p4) → p4) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51281008292931830158773272007 : (((p1 ∧ (p3 → (((((p3 ∨ (True ∨ p5)) ∨ (False → p4)) → False) ∧ (p5 → False)) ∧ True))) ∨ ((p3 → ((p3 ∨ p2) ∨ p4)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56561866528889131583551534067 : (((p5 ∨ ((p2 ∧ p5) ∧ p2)) → ((((p1 ∧ p3) ∧ ((p5 → False) ∨ ((p4 ∨ True) → p2))) ∧ p1) ∨ ((False ∨ (True → True)) ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768417619454647458758305856285 : (((p5 ∧ (((p3 ∧ p3) ∧ (p4 ∧ ((((p3 ∨ p3) ∨ p4) → (p3 ∨ (p2 ∧ p5))) ∧ (p4 → p4)))) ∨ ((p2 ∨ (False ∧ p3)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321126557021617631101152735465 : (p4 ∨ (p2 ∨ ((p3 → ((p1 ∧ (False → (((p4 → True) → p2) ∨ (((p4 → p2) → p2) ∧ p2)))) → (p5 ∨ p4))) ∨ (False → (p5 ∧ p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133811934253463726777282945764 : ((((p4 ∨ False) ∧ (p3 ∧ (((((p5 → ((p1 ∨ p1) ∨ p1)) ∧ (True → False)) → p3) ∨ (p2 → p2)) ∧ p3))) ∧ p4) ∨ (False → (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37937429574243599638927614828 : ((((p1 ∨ (((((((p4 ∧ (((True → p3) ∨ p3) ∧ False)) → p5) ∨ False) ∨ (p3 ∧ p1)) → p4) → p2) → p2)) ∧ (True ∧ False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205864239436495477173709912594 : (((p5 → p2) → ((p5 ∧ p1) ∨ p4)) ∨ ((((p5 ∧ p3) ∧ (p4 → True)) ∧ (p3 → (((p1 → False) ∧ (p3 ∧ p3)) ∨ (p3 ∨ False)))) → p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118214890200136792058394965837 : ((p1 ∨ ((p5 ∧ (((p3 ∧ p1) ∨ ((True ∧ ((((p1 ∧ False) ∨ (True ∨ False)) ∧ True) ∨ p4)) ∧ (p4 → p3))) ∧ False)) ∧ p2)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216908512631896550721661590415 : (((p4 ∨ (p2 ∨ p1)) ∧ p4) → (((p1 ∧ (True ∧ p3)) ∧ True) ∨ (p3 ∨ ((p2 → ((p3 ∨ p5) ∨ (p5 ∧ False))) → ((p1 → p1) ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338955043373155402556808768075 : (p1 → ((False → True) → (False ∨ (p5 ∨ (((p5 ∧ (p3 ∨ p5)) ∨ (p4 ∨ False)) → ((True → ((p5 → ((p4 → False) → p4)) ∨ p5)) ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587716613971457787323747675575 : ((((((p4 ∧ ((True ∧ p2) → (p2 → ((((((((p1 → p2) ∨ p4) ∧ True) ∧ False) ∧ True) ∨ p1) ∨ p2) ∨ p5)))) → False) ∨ p4) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247971618387260410866848757649 : ((p1 ∨ p4) ∨ ((((((((p5 ∨ (True → p1)) → (p5 ∧ p2)) ∨ p3) ∧ (False ∧ p2)) ∧ False) ∧ p2) ∧ p4) ∨ (((p5 ∧ p2) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_755742776559368529347947548234 : (((p1 ∧ (((p2 ∧ p2) → ((p4 ∨ ((p4 ∧ p5) ∨ p4)) ∧ ((p4 ∧ (p5 → ((True ∧ False) → (True ∨ p2)))) ∧ (False ∧ p3)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44923600046833774832935701094 : ((((p1 ∧ p1) ∧ (((p5 → ((((True ∨ p4) ∧ False) → p1) → (p1 ∧ ((False → p5) → ((p1 ∨ p2) ∨ p4))))) → p5) ∨ p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798771784082184328018909870130 : (((p1 → (((p1 → p4) ∧ p2) ∨ ((p2 ∨ False) ∨ ((False ∨ ((p2 ∧ False) ∧ p2)) ∨ ((((False ∨ p4) → p3) → True) ∨ (True ∧ p5)))))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137817380877689461759081156736 : ((p3 ∨ (((p3 ∧ ((p4 ∧ p1) ∧ (((p3 ∨ p5) ∨ p2) → False))) ∧ ((False ∧ ((p4 → p4) ∨ p3)) → p4)) ∨ True)) ∨ ((p5 ∨ p4) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185864867145135940683516082355 : (((((True → (True → ((p1 ∨ p1) → False))) ∨ False) → p4) ∧ p2) → (((p1 → (True → p3)) ∨ p3) ∨ (True ∧ (p2 → (p4 ∨ (p5 ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684225384474162909425899320609 : (((((True ∧ (((((p2 ∨ True) ∧ p3) ∧ False) ∧ p4) → (p2 ∧ (p5 → p2)))) → (p4 ∨ p2)) ∨ ((p2 → p3) → (p1 ∨ (p5 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199605074182441180051165079704 : ((((False ∧ (p4 → (True → p4))) → p5) → p4) → (p3 ∨ (((p3 ∧ p2) ∧ (p3 ∨ (p4 ∨ (p5 ∧ ((p5 ∧ p5) → p3))))) ∨ (p4 → p4)))) := by
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
theorem thm_5_vars_61985051041378122672009630775 : ((p2 ∧ (((p4 ∨ p4) ∧ ((False ∨ (True → p2)) → p5)) → ((((False → p1) → p1) ∧ (p4 ∨ (p5 ∨ ((p4 ∨ p2) ∧ p1)))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191733540106605433921633016333 : ((False ∨ (((p5 ∨ ((p1 → p5) ∧ False)) ∧ p4) → p2)) ∨ (((p5 → (((False ∧ p5) ∧ p4) ∨ True)) → ((p4 → (p1 ∧ p5)) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310303673709092800734375249573 : (p2 ∨ (((False ∧ (p1 ∨ p2)) ∨ (p5 ∨ (p4 ∧ (True ∧ p2)))) ∨ ((p5 ∨ True) → (False ∨ ((True → ((True ∨ False) ∨ (p4 ∧ p3))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172718147131363167370168871633 : (((p5 ∨ False) ∨ ((p2 ∧ (p5 → p1)) → ((p1 ∧ ((p3 → p5) ∨ True)) ∨ p5))) ∨ (((p3 ∨ False) → (p3 ∨ (p1 ∧ (p1 → True)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177722249839329954139631209238 : ((((((True ∧ p4) → True) → True) ∧ ((False ∧ (p5 ∨ True)) ∧ p4)) ∧ p4) ∨ ((((p1 → False) ∨ p1) ∨ p1) → (p4 ∨ ((False → False) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807602905803071960979424592439 : (((p4 → (((p2 ∨ p2) ∨ (p2 ∧ p3)) ∨ (((p4 → p4) ∧ (((p3 → (p4 ∧ p3)) ∧ (p5 ∧ p1)) ∨ (True ∨ (False → p3)))) ∨ p5))) ∨ p3) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157401725321555656309509275301 : (((((((p2 ∧ p5) ∨ (False → (p3 → False))) ∨ p3) → (p3 ∨ False)) ∨ (p2 → p1)) ∧ (False ∨ False)) ∨ (p5 → (False → (p4 ∨ (True → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191838843321316540144873341834 : ((p3 ∨ ((p4 ∨ (p2 ∨ False)) ∧ (p5 → (p5 → p2)))) ∨ (p1 → ((p1 ∨ (False ∨ ((p4 → False) ∨ p4))) ∧ (((p2 ∧ p1) ∨ p2) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337785534947521493961435075288 : (p1 → ((p5 → (p2 → (((p5 → (p3 → p2)) → p1) → (p3 ∧ ((p4 ∧ p5) ∨ False))))) ∨ (p1 → (((False ∧ (p1 ∨ True)) ∨ p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166242616573416929341202047567 : ((p2 ∧ (p4 → ((p2 ∧ (True ∧ (False ∧ (p5 → (p5 ∨ (False ∨ (p2 → False))))))) ∧ p5))) ∨ ((p2 ∧ (p5 → p2)) → (p5 ∨ (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590968537262758224085099266452 : (((((p2 → (((((((p5 ∧ ((p4 → (p5 → (p2 ∧ p2))) ∨ p4)) ∧ True) ∧ (p3 ∨ False)) ∨ p5) → False) ∨ p4) ∧ True)) → p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218331923468575822935314596879 : (((False → p3) ∨ (p2 ∨ p5)) → ((p3 → p5) ∨ ((((((p4 ∧ p4) → ((p1 ∨ p2) ∧ p2)) ∨ (True ∧ (p4 → False))) ∧ p2) → True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66075896819583940174585586187 : ((p5 ∨ ((p2 ∧ ((((p1 ∧ p2) ∧ ((True ∨ False) → (True ∧ True))) → (True ∨ (p3 ∨ True))) → ((True → (p2 → False)) → p5))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233276927112698546810945357592 : ((True ∨ (True ∨ False)) → (((p5 ∧ (True ∧ p3)) ∨ (((((True → p3) ∧ (p5 ∧ False)) ∧ ((True → p1) ∧ (p3 ∨ p4))) ∧ False) ∨ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777539969632020310588139935017 : (((p1 ∨ (((((True → p4) ∨ p3) ∧ p4) ∧ (p3 ∨ (p4 ∨ (p5 ∨ p2)))) ∧ (False ∧ ((False ∧ (False → (p1 → p1))) ∨ (p1 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137943505798956309812522053836 : ((p5 ∨ ((((((p5 ∧ p3) → p2) ∧ ((False ∧ p2) ∧ False)) → p1) → ((p5 ∧ ((p5 → p1) → True)) ∧ False)) ∧ p3)) ∨ (p5 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228646275441743253236827315256 : ((p2 ∨ (p1 ∧ p3)) ∨ ((p1 ∧ (False → p4)) → ((((p5 ∧ p1) ∨ (((True → p2) → p3) ∧ p1)) ∧ p4) ∨ (p2 → ((False → False) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689518439448014835967712048498 : (((((p1 ∧ (((p1 ∧ p2) → (p5 ∧ True)) ∧ p5)) ∧ (p5 ∧ ((p5 → p4) ∧ p5))) ∨ (((p2 → (p5 → False)) ∨ p3) ∧ (p2 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50810849087187757380326948569 : (((p3 → ((p2 ∨ ((p3 ∧ (True → ((False ∨ (p1 ∧ False)) ∧ True))) ∨ (False ∧ True))) ∧ (p4 ∧ False))) → ((True → (p1 ∧ p4)) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114654552628625318171645201951 : ((((p3 ∧ ((p2 → (p5 ∧ (False ∧ False))) ∨ True)) → ((True ∨ p5) ∧ (p3 → p2))) ∨ ((p2 ∧ (p5 ∧ False)) ∨ (p3 ∨ p4))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193542686523706656366601727239 : (((p1 ∧ p4) → ((((False → p1) ∧ p2) ∨ p4) ∨ True)) → ((False ∨ (p4 → True)) ∧ (((p4 → (p2 → (p4 → True))) → p2) ∨ (True ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198396738521532762640901931291 : ((p3 ∧ (p5 ∨ (((p1 ∧ p2) → True) → p2))) ∨ ((((p1 ∧ p4) → p4) ∨ (((p5 ∨ (p1 ∨ p3)) ∧ ((p5 ∨ p2) → False)) ∨ True)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198377679045619910585876554021 : ((p3 ∧ (((p4 ∧ p4) ∧ p5) ∧ (p2 ∧ p4))) ∨ ((True ∨ p1) ∨ (((p2 → p1) ∨ (((p2 ∧ (p3 → True)) → (p4 ∨ p4)) ∨ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



