variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301161418013071925428056182702 : (False ∨ ((p3 ∨ ((p1 → (p4 → p5)) ∨ (p2 ∨ p3))) ∨ (((p2 → ((p1 ∧ (p4 → (p1 ∨ (p2 ∧ p5)))) ∧ p3)) ∧ p2) → (p2 → p1)))) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57360384802734624585948018458 : (((p3 ∧ (p4 → p5)) ∨ ((((p4 ∨ True) → ((((True ∧ p1) ∨ p3) ∨ True) ∧ (p1 → (p5 ∨ p1)))) ∨ p4) ∧ ((p1 ∧ p1) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769723549464541259141822495073 : (((p5 ∧ (p2 ∨ ((p3 ∧ ((((p5 → ((False ∧ False) ∨ ((False ∨ (p2 ∧ p5)) → ((True ∧ p5) ∧ False)))) ∧ True) ∨ True) → p3)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49093654552533274642165258478 : ((((((False ∧ (((False → p5) ∧ p4) ∨ (p5 → (p3 → p4)))) ∨ p4) ∨ (False ∧ p4)) ∨ (p5 ∧ (p2 ∧ p1))) ∨ (True → (False ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196276990288542958574489451424 : ((p3 ∨ ((((p5 → p5) ∨ p3) → p1) ∨ True)) ∧ ((((p4 ∧ p5) ∨ p2) ∨ (((False ∧ True) ∧ (((p5 → p2) ∧ False) → p5)) → p4)) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94974534706547176192416261801 : ((p4 ∧ ((((p2 → ((((False ∨ ((((p3 → (p1 ∧ False)) → False) ∧ False) ∨ p2)) ∨ True) ∨ p2) ∨ (False ∨ p3))) ∧ True) → False) ∧ p3)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → ((((False ∨ ((((p3 → (p1 ∧ False)) → False) ∧ False) ∨ p2)) ∨ True) ∨ p2) ∨ (False ∨ p3))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125332736180370941779305819372 : (((True ∨ (True ∧ p4)) → ((((p4 ∨ (p1 ∧ p5)) → (p2 ∨ ((((p5 → (p4 → True)) ∨ p5) ∨ True) ∧ True))) → p3) ∧ False)) → (p2 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (True ∧ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67872374635617293346615112631 : ((p2 → (((p3 → ((p4 → (((p3 ∨ True) ∨ (((p4 ∧ p4) → p4) → p3)) → p5)) → True)) ∧ (True ∨ p2)) → ((p5 ∨ p4) ∨ p2))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307730587608301477092909920667 : (p1 ∨ (p3 → ((p5 ∨ (((p5 ∧ (p2 → True)) → ((p2 ∨ (p3 → (True → p5))) → ((p2 → p4) ∨ p3))) ∨ ((True ∨ p4) → p3))) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677393922277737651091180188134 : ((((((((((True ∨ True) → p5) → p3) ∧ p3) ∨ ((p2 ∨ (p3 ∨ (p5 → p2))) ∧ p3)) ∨ p1) ∨ False) ∨ ((False → True) ∨ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711792806380804149924476008840 : ((((((p2 ∨ (False ∧ True)) → p1) ∧ False) ∨ (((p5 ∨ (p3 ∨ (p2 ∧ p4))) ∧ ((p5 ∨ p5) ∨ (p5 ∨ p3))) → (p4 ∨ (p2 → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265720355242143317880062646143 : (True ∧ (p3 ∨ ((False → (p1 ∧ ((False → (p1 ∧ p4)) ∧ False))) → ((((p5 ∧ ((False ∧ True) → True)) ∧ (p3 ∨ p1)) ∨ (True ∨ p5)) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116721101028736368895292273246 : (((p2 ∧ p3) ∨ (False ∨ (p3 → ((((p1 ∧ ((True ∧ p1) ∨ (p1 ∨ p5))) ∧ (p1 ∨ True)) ∧ True) ∨ (p3 → (p3 → p3)))))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57333287726305526644609025903 : (((p1 ∧ (p2 ∨ False)) ∨ (p2 → ((p5 ∨ (((True ∨ p1) → (p1 ∧ (p1 ∨ True))) ∨ ((True → p5) → (p1 → p5)))) ∨ (p1 ∨ True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113099281167434790404741538785 : (((True → ((p2 ∧ (((True ∨ (((False ∧ (p2 → (p4 ∧ True))) ∧ p2) → p5)) ∧ (False → p4)) ∧ (p1 → p4))) ∧ p4)) → p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606932022731797545739968786131 : ((((((p2 ∧ ((p4 ∧ (False ∧ (p2 ∧ False))) ∨ (p3 ∧ ((p2 → p1) ∧ (True → True))))) ∨ (p2 → ((p1 ∧ p5) ∨ p3))) ∧ p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172001833999343465834359143948 : (((((False → (True ∧ p2)) ∨ (p4 → (False → (True → True)))) → p4) ∨ (p1 ∧ p2)) ∨ (False → (p1 ∨ ((p4 ∧ ((True ∧ True) → p4)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51146191630804294770782718967 : ((((((True → p1) → (((True → p3) → p4) ∨ p2)) ∧ ((p1 → p4) ∧ (p2 → p4))) → p5) ∨ ((p2 ∨ p1) → ((p5 → p4) → True))) ∨ p4) := by
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
theorem thm_5_vars_57380410332459745785046020788 : (((p5 ∧ (p1 → True)) ∨ ((p3 ∨ ((((p5 → (p2 ∨ p4)) → (p3 → p3)) ∧ p4) ∧ p1)) ∨ (True ∧ (False ∨ ((p2 ∨ p5) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8372105781031638918803256320 : (((((p5 ∨ (p4 ∧ (p3 ∨ p1))) ∨ ((((p4 ∨ ((p2 ∨ ((p2 ∨ p5) ∨ p2)) ∧ (p1 ∧ p2))) → p2) ∧ p5) ∨ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719047269200701738704769038229 : ((((True ∧ ((p1 ∧ p5) ∨ p1)) ∨ (p3 ∨ ((((True → (((True → True) ∨ p2) ∨ p3)) → (p1 ∨ False)) → ((p1 ∧ False) ∧ True)) ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_547949701740496362174624264515 : (((False ∨ (((p4 ∨ p2) ∨ (True ∧ (((p3 ∨ p1) ∧ p4) ∧ (False ∧ (p1 ∨ (False ∧ False)))))) → (p2 → (p5 ∨ ((p1 ∨ False) ∨ p2))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h10.left
      let h15 := h10.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h10.left
      let h18 := h10.right
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684755446700289794480415110801 : (((((False ∧ p2) ∨ ((((p5 ∨ True) ∨ (((p5 → p4) ∧ (p5 ∨ p4)) ∨ p1)) → p5) ∧ p5)) ∨ (p1 → ((p1 ∨ p4) → (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807858717990440598829310794033 : (((p4 → ((True ∧ p1) ∨ ((((False ∧ (p4 ∨ False)) ∨ (((p3 ∧ (p5 ∨ False)) ∧ p2) → (p3 ∨ True))) → ((p2 ∧ False) ∧ p3)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66344247209345492635351056499 : ((p5 ∨ (p4 ∧ (((True ∧ (True ∨ ((p1 → p4) → p1))) ∧ (p5 ∨ (True ∨ p3))) → (p2 ∨ (((p4 ∨ (p4 → p2)) → False) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346362490646439326036256863336 : (p3 → (((p3 ∧ p3) → (p1 ∨ ((p1 ∧ (p5 ∨ p2)) ∧ (((p2 ∧ True) ∨ (((p5 → p4) → p1) → p2)) ∨ (p3 ∨ False))))) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49310962210643907409495315373 : (((p2 ∨ ((((((p1 → p2) → (False ∨ ((p1 ∧ (p3 → (p3 → p3))) → p5))) → p4) ∨ p5) → p2) ∨ p2)) ∨ ((p1 ∨ True) ∨ p5)) ∨ False) := by
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
theorem thm_5_vars_248863863497987051975288258425 : ((p3 ∨ p5) ∨ ((((((p2 ∨ ((False ∨ (((False ∧ p3) ∨ (p5 ∨ (True → (p5 → True)))) ∨ p2)) ∨ p5)) ∨ p4) ∧ True) ∨ p4) ∨ p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260483097524704662185247365992 : ((p3 → False) → ((False ∨ (p4 ∧ (False ∨ ((((False ∨ p3) ∨ ((False ∨ (p4 ∨ p5)) → True)) → p3) ∨ p3)))) → ((p3 → (p5 ∨ True)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : ((False ∨ p3) ∨ ((False ∨ (p4 ∨ p5)) → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h21 := h18 h19
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h25 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h26 := h1 h25
        -- False on the left can always be used.
        apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350998515110920456115801887118 : (p4 → ((p5 ∧ ((p4 ∨ True) → (p2 ∨ (p2 ∧ ((((p4 ∨ (p5 ∧ p4)) → True) → True) → (((False ∨ False) ∧ p3) → True)))))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651825731360735913778530060894 : (((((p4 ∧ True) → ((p4 ∧ (p5 ∧ (p3 ∧ (((((p1 → (p1 ∧ p1)) → p1) ∧ (p5 → p2)) ∨ p4) → False)))) ∨ True)) ∧ (True ∧ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117197403156835279978280717164 : ((True ∧ (((((True → ((p5 ∧ p4) ∨ (p1 ∧ p4))) ∨ p5) ∨ False) ∨ (p3 ∧ p3)) → ((p2 ∨ ((False → p4) → p1)) ∨ True))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643613740074480226895111647421 : ((((p4 ∧ (p5 ∨ ((p5 → (((p3 → (p1 ∨ ((True → (p4 ∧ True)) → ((True ∨ (p5 ∨ p1)) ∨ p3)))) ∧ p4) ∨ p1)) ∧ p3))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153572405061871911310136277319 : ((False → ((p5 ∨ ((p5 → ((p1 ∧ False) ∧ p3)) ∨ (p5 → ((True → ((p4 ∨ False) ∨ False)) ∧ p1)))) ∨ p5)) → ((p3 ∧ (p4 ∧ True)) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354630308901248578949833547666 : (p5 → (((p1 ∨ ((((((True → (p2 ∨ False)) ∨ False) ∨ False) ∧ ((True ∨ p1) ∨ p1)) → (p4 ∨ p2)) ∨ (True ∧ (p5 ∧ p1)))) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204447477795717644653847018418 : (((((p4 ∨ p2) → p4) ∧ True) ∨ p1) ∨ (((False → (False → p3)) → ((p5 → ((p2 → True) ∨ (p4 ∨ False))) ∧ p5)) → (p5 ∨ (p3 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (False → p3)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304996583338762874201754587466 : (p1 ∨ (((p2 ∧ ((p4 ∧ p4) ∧ ((p3 ∨ (p2 ∨ (p4 → p3))) ∨ ((p2 ∨ p4) ∨ (p4 ∨ p1))))) ∨ (True ∨ False)) ∨ ((False ∧ p5) ∧ p3))) := by
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
theorem thm_5_vars_57507867296706786335922012782 : (((p3 → (p5 ∧ p5)) ∨ (((p1 → (p3 → ((True ∧ ((p4 ∨ p1) → True)) → p2))) → p5) ∨ (p3 ∧ ((p1 → (p4 ∨ True)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255304244446616107629703897562 : ((p5 ∧ True) → (((True ∧ p4) ∧ (p1 ∧ ((p3 ∨ p2) → ((p4 ∨ p5) → ((p4 → ((p1 ∨ p4) ∨ (p4 ∧ p5))) ∨ (p5 → p4)))))) ∨ p5)) := by
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
theorem thm_5_vars_682974582540471066056783019007 : (((((True ∧ p5) → (((p5 ∧ ((((p3 ∨ p2) ∨ False) ∧ (p4 → p2)) ∨ p3)) ∧ p3) ∨ p2)) ∧ (((p4 ∨ (p4 → p5)) ∧ p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164568908345430420852469708847 : (((((p2 ∨ p3) ∧ p3) ∧ (p2 ∨ (((p5 ∧ False) ∨ p2) ∧ ((p3 → p2) ∨ p1)))) ∧ False) ∨ ((p2 → ((p4 → (p2 → p2)) → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64889229867595911736868044767 : ((p2 ∨ ((((((True → ((p4 ∧ p2) ∨ (p5 ∧ p5))) ∨ ((True → p3) ∧ p1)) ∨ p4) ∨ (p5 ∧ True)) ∨ True) ∨ ((False ∧ p1) → p2))) ∨ p1) := by
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
theorem thm_5_vars_40722718023167697963025567584 : (((((p1 → (True ∨ ((p5 ∨ p5) → p4))) ∧ (p1 ∧ ((((p3 ∧ p4) ∨ p1) → (True ∧ p4)) ∨ (p2 → (p5 ∧ p5))))) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802719128558405139016573308048 : (((p2 → (p1 → (False ∧ ((False ∧ (True ∨ (True → (((p1 ∨ ((p2 ∨ (p4 → ((False ∧ p2) ∨ False))) → True)) ∨ False) ∧ False)))) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123593452071796287582444555058 : ((((False ∨ p2) ∧ (p4 → (((p4 ∨ ((p2 ∨ True) ∨ (p4 ∨ p4))) → True) ∧ p5))) ∨ (((p3 ∧ (True → p1)) → False) → p1)) → (p1 → p1)) := by
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
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148075061557940414395706234759 : (((((p5 ∧ p2) → ((p1 ∧ p2) → ((p3 ∧ (p1 ∨ False)) → (True → (p1 ∨ p3))))) ∧ p5) → (p3 ∧ p3)) ∨ ((p4 ∧ p3) → (p4 ∧ p4))) := by
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
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166958511920855618371517916748 : (((True ∧ (p5 ∨ (((((p3 → True) ∨ p3) → p5) ∨ p4) → ((False ∧ p4) → p1)))) ∧ p3) → ((p1 ∨ (p5 → False)) ∨ (p3 ∧ (False ∨ p3)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178217696212484102645165104690 : (((p5 ∨ (p1 → (((True ∧ (p1 ∧ (p4 ∨ True))) ∧ p2) → p5))) → False) ∨ ((False → (p5 ∨ (p1 ∨ ((False → p2) ∧ (p4 → p1))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205835517880176783022628877423 : (((False → p4) → (p3 → (p4 ∨ p4))) ∨ ((p3 ∧ (p2 ∧ (True → False))) ∨ (p5 ∨ (((p4 → False) ∧ p3) ∨ ((True → (False ∧ p1)) → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260623039070896017104755215707 : ((p3 → p2) → (True ∧ (p1 ∨ (p5 ∨ (((((False → (p3 → p1)) ∨ True) ∧ (p4 ∧ (p3 ∨ ((p1 → (p1 → p4)) ∧ p4)))) ∧ p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_316609135854964065830507045955 : (p3 ∨ (p4 ∨ ((((p1 → (((False ∧ (p2 ∨ ((p5 → (p1 ∨ (p3 ∨ p2))) ∧ p2))) ∧ True) ∧ (p5 → True))) ∧ p4) → (False ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253734840436218333755398558667 : ((p1 ∧ p1) → (((((p3 → ((((p3 ∧ (p4 → p1)) ∧ (p1 → p2)) → False) ∨ p3)) ∨ p2) → ((True → p2) ∨ p2)) → p2) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_168713305001100485014785845063 : ((True ∨ ((False ∨ (p4 ∨ (p5 → p3))) ∨ (p1 ∨ (p2 → (p4 → ((p4 → p3) ∨ p1)))))) → (p3 → (((p1 → p2) ∨ True) ∨ (p1 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258359869094848424585653924994 : ((p5 ∨ False) → (((False ∨ ((True → (p3 ∨ p4)) ∧ (False ∨ p2))) → ((False → p5) → p3)) ∨ ((p5 → False) → ((p2 → False) ∧ (p2 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68282754095317763038876338780 : ((p3 → ((p3 → (True ∨ (((p2 ∨ p3) ∧ ((p5 → True) → ((p3 ∨ p3) → ((p4 ∧ True) ∧ (p5 ∨ True))))) → p4))) → (p4 ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65791657569847035350177397771 : ((p4 ∨ ((((True → False) → ((p5 ∧ p1) ∨ (p4 ∧ (p2 → False)))) → False) → ((p5 ∧ ((True ∧ ((p5 ∧ p2) ∧ False)) → p4)) → p1))) ∨ p5) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : ((True → False) → ((p5 ∧ p1) ∨ (p4 ∧ (p2 → False)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h5
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189257971775300083988425749523 : (((p1 ∧ p3) → (p1 ∨ (((p2 → False) ∨ p2) → p5))) ∧ ((p4 → ((p3 ∨ ((p1 ∧ p2) ∧ p3)) ∧ p4)) ∨ ((True → p1) → (p1 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729201964741070012407132755110 : (((((p3 → p2) ∧ p5) → (((p3 ∧ p1) → True) → ((p3 ∧ (p1 → (((True ∧ p4) → (((p2 → p1) ∧ p5) ∨ p3)) → p2))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233481762917297900058270348231 : ((p1 ∨ (False ∧ p3)) → ((((p1 ∧ (False ∧ p1)) ∧ (p2 → p4)) ∧ (p5 → (True → (p5 → (p4 → (p3 ∧ (True → (p3 ∧ p4)))))))) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135542825971847437254142408858 : ((((((p2 ∨ False) → (False ∧ p4)) ∧ p1) → (((p4 → (p5 → False)) ∨ p1) ∨ p2)) ∧ ((p2 ∨ (True ∨ p1)) ∧ p5)) ∨ ((p1 ∧ p4) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319201983411807094534203563463 : (p4 ∨ ((((p2 ∨ (((p3 ∨ (((p4 ∧ True) ∧ True) ∧ p1)) ∨ p4) ∨ False)) ∧ True) ∧ (p5 ∨ p5)) → (p2 ∨ (p2 ∨ (True ∧ (p5 → True)))))) := by
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
    cases h3
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h14
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h18.left
          let h21 := h18.right
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h25
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- Implications on the right can always be decomposed.
            intro h27
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h30
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Implications on the right can always be decomposed.
          intro h32
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h33 =>
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352543274815779851747392927014 : (p4 → ((True ∨ False) ∧ ((((p3 → (p5 → (p2 ∧ p2))) ∨ p2) → ((p5 ∨ p1) → (p5 ∨ ((p3 ∨ p5) ∧ ((p1 ∨ False) → p4))))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322382379191859339188533118407 : (p5 ∨ (((p4 ∧ (p3 ∨ ((p4 → (p2 ∧ p2)) ∨ ((p1 → False) ∨ (p1 → (p2 → True)))))) ∧ (p5 → ((p1 ∨ p2) → (p1 → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702017007057170230269307751000 : ((((True → (((p3 ∨ ((p4 ∧ p5) → False)) ∨ p4) ∨ False)) ∧ ((((p4 ∨ True) ∧ p3) ∧ (True ∨ True)) ∨ (((False ∧ False) ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113724101526624792050095320471 : ((((((True ∨ (True → ((p3 ∨ p5) → True))) ∧ (p4 ∧ p5)) ∨ ((p4 → p2) ∧ p1)) ∧ (p2 → (p5 ∨ False))) → (False ∨ p4)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_393828591963610048545970414962 : (((((p2 ∨ p4) ∨ (p2 ∨ (((((p4 → (False ∧ p5)) ∨ (p1 ∧ p1)) ∨ False) ∧ False) ∨ ((p4 ∨ ((p2 ∧ True) ∧ False)) → True)))) ∨ False) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303346768928910548857912418284 : (p1 ∨ (((True ∧ ((((p5 ∨ p4) → ((((False ∧ ((True ∧ p2) ∧ (False → p2))) ∧ p2) → (True ∨ p5)) ∨ p1)) → False) ∧ p1)) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_134006311448998108405601863042 : ((((p2 ∧ (p4 ∨ ((False ∨ (p3 ∨ p5)) ∧ ((False → (p4 ∧ (p3 ∨ (False ∨ (p5 → p5))))) → True)))) ∧ p1) ∨ True) ∨ (False ∨ (False → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655794993984813459396188121672 : (((((p3 ∧ (p3 ∨ ((p2 ∧ (p5 ∨ (p5 → (p5 ∧ ((p4 ∧ False) ∨ False))))) ∨ (p5 ∨ p4)))) ∨ ((False ∨ p2) ∨ True)) ∨ (p3 → p5)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157743329152513829991703944547 : ((((p5 ∧ ((p3 → (True → (p2 ∧ (p5 → p1)))) ∨ p5)) ∨ p2) ∧ (((p5 ∨ p4) ∨ p2) ∨ True)) ∨ ((p1 ∨ p5) ∨ ((p4 ∨ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698440354573404117631829792605 : (((((p3 ∨ ((p1 → (True ∧ True)) → p5)) ∧ (p1 ∨ (p2 ∧ p5))) ∨ (p4 ∨ (((p3 ∨ False) → (p3 ∧ (False ∨ (p3 ∨ p5)))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57942847374921975977112030678 : (((False → (p1 → p4)) → (((True ∧ ((False ∨ ((p4 ∨ (p1 ∧ p4)) ∨ p3)) ∨ (True → (p1 → p4)))) ∨ ((p3 ∧ p5) → p5)) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626150148321033550860882037837 : ((((p3 → ((((p4 → (((p1 ∧ True) ∧ (p4 ∨ ((False ∧ (p2 → p3)) ∨ ((True ∨ False) ∧ p4)))) ∨ p2)) → False) → p4) ∨ p2)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_224539828815716141012998845815 : ((p2 → (True ∨ p1)) ∧ ((p2 ∨ False) ∨ (p2 ∨ ((p3 → ((p3 ∧ (False ∨ True)) ∧ p2)) ∨ ((p3 → False) ∨ ((False ∧ p2) → (p4 ∨ p3))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_171711480782526761596553995297 : (((p5 → (False ∧ ((p5 ∨ (p2 ∧ (False ∧ p2))) ∧ (False ∧ (p4 ∨ p5))))) ∨ p2) ∨ (((p3 → (False ∨ p3)) ∨ (p3 ∧ (p1 ∨ True))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62046330604666313152436779744 : ((p2 ∧ ((p3 ∨ p2) ∨ ((p1 ∨ ((p3 ∨ (p1 ∨ p5)) → False)) ∨ ((p3 ∧ p4) → (True → (p2 ∨ (False → ((False ∧ p1) → p2)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161187009494262422949665456130 : (((p2 ∨ p1) ∨ (p5 ∨ (p2 ∧ ((((((p4 → p3) ∨ p4) ∨ p3) → p2) → p2) ∨ (p2 → True))))) → (p5 ∨ (True ∧ (False ∨ (False → p4))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231431061675294290018962250477 : (((p2 → True) ∨ p5) → ((p3 → ((p4 → (((p1 ∧ (False ∨ p2)) ∧ (False ∧ p2)) ∨ (p4 → ((p1 → p2) → p4)))) ∨ True)) ∧ (p2 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231640626197006302403780235989 : (((False ∧ p2) → False) → ((p3 → (p4 ∨ (p3 ∧ (True ∧ (p2 ∨ (((p4 → False) → (True → (False ∨ (p4 ∨ (p1 ∧ p3))))) → False)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793709004026102645711775518099 : (((True → (True → (((p2 → p2) ∨ p5) → ((((((p4 ∨ True) → p1) → False) ∨ p4) ∧ p2) ∨ ((p4 → (p1 → (p5 ∧ True))) ∨ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606888383355066696732989716338 : ((((((p3 ∧ (((True → (p1 ∧ p1)) ∧ (((p4 ∨ p5) ∨ (p4 → (False → p2))) ∨ p5)) → False)) → (p4 → (p1 ∨ p2))) ∧ p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310666714334979862989986499109 : (p2 ∨ (((p3 ∧ (p3 ∨ p4)) → p3) → ((p2 ∨ p1) → (((False ∨ (p5 ∨ (p5 ∨ p5))) ∧ p2) → ((False ∨ (p2 → (True → p4))) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h12 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h13 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h12
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h14 := h6 h13
          -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h14, we can now drive its conclusion.
          let h16 := h14 h15
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h18 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h8
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h19 := h6 h18
          -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
          have h20 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h19, we can now drive its conclusion.
          let h21 := h19 h20
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h2
          case inl h24 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h25 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h24
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h26 := h6 h25
            -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
            have h27 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h26, we can now drive its conclusion.
            let h28 := h26 h27
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h29 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h30 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h8
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h31 := h6 h30
            -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h31, we can now drive its conclusion.
            let h33 := h31 h32
            -- One of the premise coincides with the conclusion.
            exact h33
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h2
          case inl h35 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h36 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h35
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h37 := h6 h36
            -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
            have h38 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h37, we can now drive its conclusion.
            let h39 := h37 h38
            -- One of the premise coincides with the conclusion.
            exact h39
          case inr h40 =>
            -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
            have h41 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h8
            -- We have shown the premise of h6, we can now drive its conclusion.
            let h42 := h6 h41
            -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
            have h43 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h42, we can now drive its conclusion.
            let h44 := h42 h43
            -- One of the premise coincides with the conclusion.
            exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227437745481273955232406415295 : (((p5 → p3) → p4) ∨ ((p2 → (p1 → (((((True ∨ p3) ∨ (p1 → p4)) → False) ∧ p4) ∨ (False → (p1 → (True ∨ (p5 ∧ False))))))) ∨ p2)) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32010069838433074768996829157 : ((p1 ∨ (((p2 → False) ∧ (True → ((((True → ((p1 → (p3 ∨ p4)) ∨ p3)) ∨ p4) → (p5 ∧ (True → p2))) ∧ (True → True)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_124747911119760934467594484188 : ((((p1 ∧ p5) ∨ (True ∧ p2)) ∧ (((p2 ∨ ((p1 → p1) → p4)) ∧ (p5 ∨ True)) → (p4 ∧ (((True → p5) → p4) ∧ p3)))) → (p4 → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : ((p2 ∨ ((p1 → p1) → p4)) ∧ (p5 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h10 := h4 h8
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : ((p2 ∨ ((p1 → p1) → p4)) ∧ (p5 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We need to get the right conjuct of h18 based on <expert-advice>.
    let h19 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303918645113388971600699294747 : (p1 ∨ ((((p4 → True) ∨ ((((False → True) → p1) → p4) ∧ False)) ∧ (p1 ∧ ((p4 ∧ (p3 ∧ p1)) ∨ ((p3 → p3) → (p4 ∨ p3))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639544087381580928575054456073 : ((((((p1 → p1) ∨ True) ∧ ((False → (False → p4)) ∧ ((p4 ∨ (False ∧ (p1 ∧ p1))) ∧ (p2 ∧ (p4 ∧ ((p3 → p2) ∧ p2)))))) → p4) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h23.left
      let h26 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- False on the left can always be used.
      apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59074012593455228518761718148 : (((p5 ∧ False) ∨ (p3 → (((((p1 ∧ True) ∨ (p4 ∨ p3)) → (((p1 ∨ p4) → (p5 ∨ False)) ∧ p5)) ∧ p5) ∨ (p4 ∧ (p3 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218458858142715810040033243798 : (((p5 ∧ False) → (p1 ∧ p5)) → (p4 ∨ (((p1 ∧ p3) ∧ p5) → ((p4 → False) ∨ ((p3 ∧ False) → (((p4 ∨ True) ∨ (p4 ∨ p2)) ∨ p5)))))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259868718920146551609704544709 : ((p1 → p4) → ((((p2 ∧ (False ∨ (((p1 ∨ p4) → (True ∧ ((p5 ∨ (p2 ∨ p3)) ∧ True))) ∧ False))) ∨ True) → (False ∧ p5)) ∨ (False → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37720913810250949014804911606 : (((((((p3 ∨ ((p1 ∧ p4) ∧ (p1 ∧ p2))) ∧ p5) ∨ ((p3 ∧ p4) ∧ p4)) ∨ ((True ∧ (p2 ∧ (p3 → True))) ∨ False)) → False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317106716965035237212321623411 : (p3 ∨ (p5 → (((((True → p4) ∧ (p2 → p5)) → (False ∨ p1)) ∨ ((True ∨ False) ∧ ((p1 → p3) ∨ ((False ∧ p3) → p3)))) ∨ (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_642950202358811926229389073895 : ((((p2 ∧ ((p3 ∧ (p4 → (p5 ∨ ((p1 → ((p2 ∧ p2) ∨ p3)) ∧ p3)))) → (False → (p3 ∨ (p1 ∧ (p2 → (p3 ∧ p5))))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49419851178506519462205539120 : ((((p1 → (p1 ∧ (((((p3 → ((True ∧ p4) → p5)) ∨ False) ∨ p5) ∧ (True ∨ True)) ∧ (p1 → p2)))) ∧ p1) → (p5 → (p5 → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776071691524662399890376802127 : (((False ∨ (p5 → ((((p1 → False) ∨ p4) ∧ (p3 ∨ (p1 ∨ ((p4 → (((p3 → (p4 ∧ (p3 ∨ False))) ∧ p4) ∨ p4)) → p2)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346589882843171630135582585786 : (p3 → ((((((p4 ∨ False) ∨ ((p3 → p4) ∨ (p4 ∨ p5))) ∧ (((p4 ∨ p5) ∧ p4) ∨ (p2 → p3))) → False) ∨ p3) ∨ ((p4 ∧ p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148276899050807191957397844483 : (((((((((p3 ∧ (p1 ∨ p2)) → True) ∨ p4) ∧ (False ∨ False)) ∧ p2) → p5) ∨ p3) → (False ∨ (p3 ∧ p1))) ∨ ((p3 ∨ p2) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200557552797765954336882153874 : (((p3 → p1) → ((p2 → (True ∧ p5)) ∨ p4)) → ((p5 ∨ ((((p4 → (p3 ∨ (False ∧ p3))) → p4) ∨ (p3 ∨ (True → True))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726992849441803284135826114525 : (((((p1 → p3) → p3) ∨ (((((p3 ∧ ((False ∧ True) ∨ ((True ∨ p3) → (p5 → p4)))) → p2) ∧ False) ∨ p5) ∨ (p1 → (True ∨ True)))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314006549282249510737077951964 : (p3 ∨ ((False ∧ (p4 ∨ ((p2 ∧ ((p4 ∨ p2) ∨ True)) → ((((True ∨ ((p5 ∧ p4) → p2)) ∨ (p4 ∨ False)) → True) → p5)))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



