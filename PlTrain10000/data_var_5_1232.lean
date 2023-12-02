variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125567520284172467637981043915 : (((p2 → p1) ∧ ((p5 → (p4 ∨ (False ∧ (True ∨ ((p2 ∨ False) ∧ p5))))) ∨ ((p1 → p2) ∧ ((p4 ∧ p3) → (p5 ∨ False))))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166036876038905891618191090034 : (((p2 → p5) ∨ (((((p3 → (p2 ∨ False)) ∧ ((p4 ∨ False) → False)) → p3) ∧ p5) ∨ p2)) ∨ (True ∨ ((p5 ∨ p1) ∧ (p1 ∨ (p1 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165029899034410315899116994274 : ((((True ∨ (p5 ∨ p3)) ∨ (p2 ∨ ((((False → (p3 ∨ p1)) ∧ True) ∨ p1) ∧ True))) → p1) ∨ ((p3 → p2) ∨ (False → ((p2 → p1) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43673076236124077191571461493 : ((((((p4 ∧ p4) → ((p5 → (p4 ∨ (p2 ∨ (False → p1)))) ∧ (p2 → p1))) ∨ (((p5 ∨ (p2 ∧ True)) ∨ p4) ∧ p3)) → p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137841308723343070750299340405 : ((p3 ∨ ((p2 → ((((p2 → p5) → p3) ∨ p3) ∨ (True ∨ p5))) → (p5 ∨ (((p3 → (p5 ∧ p5)) ∨ p4) → p3)))) ∨ ((p4 ∧ p4) → p4)) := by
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
theorem thm_5_vars_39875937438968822219334987982 : (((p2 → (((p1 ∧ True) ∨ ((((p2 ∨ ((p3 ∧ p4) ∨ p5)) ∧ p3) ∨ True) ∧ (p5 ∨ ((p4 ∨ False) ∧ p5)))) ∧ (False ∨ True))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173193498197724441198723208191 : ((p4 ∨ (p3 → ((p1 ∧ False) ∧ ((p2 → (p5 ∨ (True → p4))) ∧ (True ∧ p1))))) ∨ (p1 ∨ ((p3 → (p4 ∧ False)) → (p2 → (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256435556832430767031668725626 : ((False ∨ p3) → (p3 ∧ ((((p2 ∨ ((p5 ∧ ((p4 ∧ True) → p4)) → p4)) → p4) ∨ (p2 ∧ (p3 → p1))) ∨ ((p5 ∧ (p3 ∨ False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299892136235732212804439822958 : (False ∨ ((True → ((((((True ∧ (((p1 ∨ p3) → p3) ∧ p2)) → p4) → (p2 ∨ p5)) ∨ (p1 ∨ (p2 ∨ p4))) ∨ (p4 ∧ p4)) ∧ False)) → p5)) := by
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
theorem thm_5_vars_705029511794106438439752601580 : ((((p2 → ((((False ∨ True) ∧ p1) ∧ p2) ∨ (p1 → p2))) → (True ∧ ((((((p4 ∧ p3) → p1) ∨ p4) ∨ p4) ∧ (p4 ∧ p1)) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115625610200902648771043289012 : (((((p2 ∨ (p1 ∧ p4)) ∧ True) ∧ p1) ∨ ((((True → p3) ∨ (p4 ∨ p4)) → ((p1 ∨ True) ∧ True)) ∨ (p3 → (p2 ∨ p2)))) ∨ (p5 → p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116193155773271657489126831131 : ((((p4 ∧ p3) ∧ False) ∨ ((p5 ∨ False) ∨ (True ∧ (((True ∧ False) ∧ (p5 → True)) → (((p5 ∧ False) → False) ∧ (p4 ∨ p5)))))) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165932088682353748947695439425 : (((p4 ∧ p5) ∧ ((p2 ∧ (p1 → p2)) → ((p1 ∧ (False ∨ (p5 ∨ p3))) ∨ (False ∧ p3)))) ∨ ((((True ∧ (p2 → p5)) ∧ False) → p3) ∨ p5)) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118622230114553291318586798116 : ((p4 ∨ ((((p3 → p2) → p4) → ((p4 ∧ p5) ∨ p5)) ∨ (p1 → (p2 ∧ (p4 → (p5 ∧ (((p1 → p1) ∧ p5) ∨ True))))))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338371395935532188128024621309 : (p1 → ((False ∧ (True ∧ (False ∧ p5))) ∨ (((((p4 → p2) ∨ p2) → False) → (p5 ∨ (p5 ∧ (False ∨ ((p1 ∧ False) ∧ (p1 ∧ p1)))))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48313576040042686643226023204 : (((False ∨ ((((p2 ∨ p5) ∧ (p3 ∨ p1)) ∨ (True ∨ (((((p5 → p2) ∨ p2) ∧ p5) ∨ True) → p5))) → (p3 ∧ True))) → (True → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p2 ∨ p5) ∧ (p3 ∨ p1)) ∨ (True ∨ (((((p5 → p2) ∨ p2) ∧ p5) ∨ True) → p5))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42520950050967712307206977350 : (((False ∨ (p5 ∨ (((((False ∨ (((((p4 → False) → (p2 ∧ p5)) ∨ False) ∧ (p5 ∧ p2)) → True)) ∧ p1) → p1) → p5) ∨ True))) ∨ False) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_225569260315637501820181437393 : (((False → False) ∧ p2) ∨ ((True → (p5 ∨ (((((p1 ∧ p4) ∨ (p1 → (p3 ∧ ((False → p3) → p1)))) → False) ∨ (p3 → p1)) → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51124653473447185495405227715 : (((((p4 ∧ (p5 ∨ False)) ∨ (((False ∧ (p3 → p2)) ∧ p1) ∨ (p1 ∧ (p1 ∨ p1)))) ∨ p1) ∨ (False ∨ (((p1 ∨ p1) ∧ True) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_117129608879354570831917860597 : (((p4 → p4) → ((((((False ∧ True) ∧ (p3 ∨ p1)) ∨ (True ∨ p5)) → p5) → ((p2 ∧ True) ∨ (p3 ∧ p1))) ∧ (p5 ∨ False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60149057940439457394270105332 : (((p4 ∨ p3) → (((p2 ∨ ((True ∧ False) ∨ False)) → (((((p2 ∨ p5) ∧ p2) → p3) ∧ (p2 ∧ (p1 ∨ (True ∧ True)))) → p5)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_681464776363011982303907866278 : ((((p4 ∨ ((p2 → p5) → ((((p2 → (((p3 → p3) ∨ (p3 ∧ p2)) → False)) → True) ∨ p3) ∧ True))) → (p3 ∧ ((p1 ∧ p1) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670666753929224184508098558003 : (((((p5 ∨ False) → ((p1 ∨ (((True → (((p2 ∨ p4) ∨ False) ∨ p2)) ∨ True) ∨ True)) ∧ ((False → p1) ∨ p3))) ∨ ((p2 → True) → False)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175788450155758018935922761871 : ((((((p4 ∨ (False ∧ (False ∧ True))) ∨ p3) ∧ (True → p4)) ∧ p3) ∨ True) ∧ ((False ∨ (False ∧ (p1 → (p4 ∨ True)))) → ((p4 ∨ p1) → p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_537851417942035615870439134 : ((((p4 ∧ ((p5 ∧ ((p5 ∧ True) → (((p1 → (p5 ∨ (p5 ∨ False))) → p1) ∧ p2))) ∧ (p4 ∨ p4))) ∧ (p1 ∧ p1)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119450599721254038527320702867 : ((p4 → (((p1 → (True → (False ∨ p2))) → p4) ∧ (((p4 ∨ (True → p5)) ∨ (p3 ∧ True)) → (p5 ∧ ((p3 → p1) → p1))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309343069412631892757757020942 : (p2 ∨ (((p5 ∨ ((((p4 ∧ (((p5 ∨ p3) → (p2 → p1)) → True)) ∨ p2) → p5) ∨ (p1 ∨ p3))) → ((True → p2) → p3)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41345348509332307896564969947 : (((((True → p5) ∧ ((((p4 → False) ∨ p3) ∧ p5) → ((True ∧ (p1 ∨ p3)) ∧ p3))) ∨ (True → ((True ∧ p4) ∨ (p4 ∨ p1)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730049593327110698398852681040 : (((((p1 ∨ p2) → p3) → ((p4 ∧ p2) → (((False ∧ p5) → (False ∨ ((p1 ∨ p3) → p3))) → (((False ∧ p3) ∨ (p4 → p5)) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172452854739392538534665993995 : ((((p2 ∨ p1) ∨ (p4 ∨ False)) ∨ (((p5 ∨ (False ∨ False)) ∨ (p1 ∨ False)) ∨ p5)) ∨ (p3 ∨ ((p3 → (p1 ∧ True)) ∨ (p2 → (False → p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190980867994437503695667536820 : ((((False ∨ (p1 ∨ p5)) ∨ p1) ∨ ((False ∧ p5) ∨ p5)) ∨ ((((True ∧ p2) ∧ (False ∨ (p1 ∧ ((p2 ∨ p3) → (True → True))))) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40428070739929432174528953056 : (((((((True → (p2 → ((p3 → False) ∨ p1))) → p4) ∨ (p4 ∧ True)) ∨ ((p5 ∧ (p3 ∨ p4)) ∧ ((p1 ∨ True) ∨ False))) ∨ True) ∨ p2) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2673651687678268319549867151 : ((p4 ∨ ((True → p4) ∧ (p2 ∧ p1))) ∨ (p2 ∨ (((p5 → (p1 ∧ ((p4 ∨ p5) ∨ (p3 ∨ (False ∨ p1))))) ∧ False) → (p1 ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51382389027129823467707326942 : (((((((p3 ∨ (p1 ∨ (p1 ∨ p2))) ∧ p4) ∨ p4) ∧ ((p2 → True) ∧ (p5 → p4))) ∨ p2) → ((True → False) ∨ (p5 → (p3 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729831504764755593846602120640 : (((((False ∧ True) → p1) → (((p2 ∨ (p1 ∧ p3)) ∨ (p1 → (p3 → (((p4 ∨ (p2 ∨ True)) ∧ (p4 ∨ p5)) ∨ (p1 ∧ True))))) ∨ p1)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80474542845205126882421155921 : (((((p1 → (p4 ∨ p5)) → True) → (((True ∧ (p1 → (p4 ∨ p3))) ∨ True) ∨ (p3 ∨ ((p1 ∨ (p5 ∨ p1)) → p3)))) → (p5 ∧ True)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → (p4 ∨ p5)) → True) → (((True ∧ (p1 → (p4 ∨ p3))) ∨ True) ∨ (p3 ∨ ((p1 ∨ (p5 ∨ p1)) → p3)))) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184206104439117749082964542372 : ((((p1 ∨ ((p4 ∧ (p3 → p5)) ∨ (p2 → True))) ∧ p1) → p3) ∨ (((((False ∧ ((True ∧ True) ∧ p4)) → p1) → p4) ∨ (True ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104360393960347485561783409301 : (((((p3 ∨ (p3 ∧ (p3 ∧ ((p1 ∧ p2) ∨ p5)))) ∨ p5) ∨ ((p4 ∨ (True ∨ (p3 ∨ (p1 ∨ True)))) ∨ False)) ∧ (True ∨ p1)) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304718499461355270293871567202 : (p1 ∨ (((((((True → (p4 → True)) → (p5 ∧ (True → True))) ∧ p2) ∨ (p4 → (False → p1))) ∧ p1) → (p3 ∨ (p3 → False))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249592953427983686992551535833 : ((p5 ∨ p3) ∨ (((False ∧ (((True ∨ p3) ∧ ((p5 ∧ (p3 ∧ p3)) ∧ ((False ∨ (p2 → p5)) ∧ (True ∨ (p2 ∧ p5))))) ∧ p2)) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197000353531323963040514016932 : (((((p2 ∧ p2) ∧ p5) ∧ (p1 → True)) ∨ p3) ∨ ((p2 ∨ True) ∧ (p1 → (((p2 ∨ (((p1 ∨ False) ∧ (p2 → False)) → p2)) ∧ p1) → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788735029308364485939268020687 : (((p5 ∨ (((p4 ∨ (p4 ∨ p3)) → (((False ∨ (True ∧ (p2 ∧ ((True ∨ p5) ∧ p3)))) ∨ (((p3 ∧ p4) ∨ p1) ∧ p4)) ∨ False)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679487296890991112103161414490 : (((((((False ∧ (p3 ∧ (False ∧ False))) ∨ (p5 → (p3 → (p3 → (p4 ∨ (p1 ∧ p2)))))) → p4) ∧ p3) → ((p2 ∧ True) → (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191206978393525050615216922090 : ((((p1 ∨ False) → p3) → ((p4 ∧ (p1 → p2)) ∧ p2)) ∨ (((False ∧ ((p2 → p1) ∧ ((p4 ∧ p3) ∧ (p3 → p5)))) ∨ p1) → (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322578760571221077563912574526 : (p5 ∨ ((p5 ∨ (((((p3 ∨ ((((p2 ∨ False) ∨ p3) ∨ p4) → p4)) ∧ (p3 → p3)) → p2) → p5) ∧ ((p5 ∨ p2) ∨ (p1 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117438768628743427625489002033 : ((p1 ∧ ((p4 ∧ ((((p5 ∨ False) ∨ True) ∨ (False → p3)) ∨ p2)) ∨ (p2 ∧ ((((True ∧ p1) ∧ False) ∧ p4) → (p5 ∧ False))))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341804520610969844643393695200 : (p2 → ((((p1 → p5) ∨ ((((p1 → ((p2 → (True ∧ (True → p4))) ∨ (p2 ∨ p2))) → (p2 ∧ p5)) ∨ p5) → p5)) → p3) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157795944065466223615878269875 : (((p3 ∧ ((((True → p3) ∧ False) ∨ (p5 → p3)) → (p3 ∨ p4))) ∨ ((p1 ∧ p4) → (True → p5))) ∨ ((((p2 ∨ p2) → p3) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357358533848294765373715389065 : (p5 → ((p5 → p1) ∨ ((((p5 ∧ p2) ∧ False) ∧ (p3 ∨ ((p4 ∧ False) ∨ ((False ∨ False) → (p5 ∨ p3))))) ∨ (((p4 ∧ p5) ∧ p1) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49958205905920338525587297811 : (((((False → ((False ∨ p2) → False)) → (False → (True → (False ∧ (p3 ∧ (p3 ∧ p5)))))) → (p5 → p2)) ∧ (p4 ∧ (p1 → (True → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42037166344630896582684958987 : ((((p4 ∧ p3) ∨ ((((((((p3 ∨ (p4 ∨ False)) → p1) → p4) ∧ p5) → (False ∧ p1)) ∧ (p4 → p2)) ∨ p3) ∨ (False → p1))) ∨ p3) ∨ p2) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591803984434095359156359676057 : ((((((p2 ∧ (p3 → (p1 → (((True ∧ (False ∨ (p3 ∧ (p5 ∨ True)))) → (True ∧ p4)) ∧ True)))) → (False ∧ False)) ∨ (p2 → p5)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234150268886122952845226410536 : ((True → (False → p2)) → (((p1 ∧ (p5 → ((((True ∨ False) ∨ (p3 → ((p4 → p4) ∨ (p4 ∨ p1)))) → p4) ∧ p1))) → p4) → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684980549927080808865970747094 : ((((p3 ∧ (p1 → ((p4 → p2) ∨ ((p3 ∨ (p2 ∨ p5)) → ((False ∧ (p2 → p3)) → p4))))) ∨ ((p5 → p1) ∨ (False ∧ (p4 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204586843407071206212788967675 : ((((p4 ∧ p1) ∨ (p3 → False)) ∨ p3) ∨ (p2 ∨ (True ∨ ((p4 ∧ ((p4 → p2) → ((p1 → p1) ∧ True))) ∨ (((True ∨ p5) ∨ True) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19194204488286890898296138671 : (((p5 ∧ ((True → ((p3 ∧ True) ∧ p3)) ∧ ((True ∨ ((p3 → p2) → (p3 ∨ p2))) ∧ p4))) → (((False ∨ p3) ∨ p3) → (True → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198527660786667290921709774754 : ((False ∨ (((p3 → p2) ∨ p1) ∧ (True → p2))) ∨ (p3 ∨ (((False → p1) ∧ (((p5 ∨ (p2 → False)) ∨ (p4 ∧ True)) ∨ (p3 ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163303148141446856473982987565 : (((((p2 ∧ p5) ∧ p5) → (p4 ∨ p5)) ∨ ((False → (True ∧ (p5 ∨ (p5 ∧ False)))) → p5)) ∧ (((p5 ∨ (p5 ∨ False)) ∨ (p1 ∨ p4)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139501182348134068234343096235 : (((((p1 ∨ ((((False ∧ p4) ∧ ((p3 → True) ∨ False)) ∨ p4) ∧ p5)) ∧ (p5 → (p3 → (p2 ∧ p1)))) → p4) → p1) → (True → (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174655666962483993455514501695 : ((((p3 ∧ p1) → p2) ∧ (((p5 ∧ ((False ∨ p5) → (p1 ∨ p4))) ∨ True) → p3)) → ((p2 ∨ p4) ∨ (p3 → ((p4 → (p2 ∨ p5)) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139172900332923410008789189386 : (((((p2 ∧ ((p2 → (p1 ∧ True)) → p3)) ∨ True) → ((p5 ∧ (p5 → p4)) → ((p2 → (p1 ∧ p5)) ∨ True))) ∨ p1) → (p3 ∨ (False ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137643811218776550792980737221 : ((False ∨ ((((p3 ∧ p2) ∧ False) ∧ (p5 → (p3 ∨ p3))) ∨ (False → ((((p4 → (p1 → True)) ∨ p5) ∧ True) ∨ False)))) ∨ (p1 ∨ (False ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595710223634731824867801624085 : (((((((p4 ∨ p3) → ((p4 ∨ (p1 → p4)) ∧ p2)) ∧ p5) ∧ ((False ∨ ((((p1 → p2) ∧ p5) → (p4 ∨ p3)) → p1)) → False)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27943465578620352370250492663 : (((p1 → p2) → (p1 ∨ (((((((p5 → (((p2 ∨ p2) → True) ∧ True)) ∧ p3) → True) → p3) ∧ False) ∨ (p1 → p1)) ∨ (p5 ∧ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138000569490364507586475677897 : ((p5 ∨ (True → (((p3 ∧ p3) ∧ ((False ∧ p5) ∨ (((((False ∨ p1) → p3) ∧ False) → (False → p3)) ∧ p3))) ∨ p5))) ∨ ((True ∧ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65637891772291352449104568614 : ((p4 ∨ ((((((p2 → ((p1 ∨ ((False ∧ False) → True)) ∨ p3)) → p3) → True) ∨ p3) ∧ (((p3 → (p1 ∨ p4)) → False) ∨ True)) ∨ p2)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48986995816765168493207995419 : (((((p4 → (False ∨ p2)) → (((((p1 ∨ p5) → (False → (p3 ∨ True))) ∧ (p1 ∨ p3)) ∧ p4) ∨ p5)) ∨ False) ∨ (p3 ∧ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191445348672380228997591955242 : (((False → False) → ((p2 → ((p3 → p3) ∨ p3)) → p5)) ∨ ((p1 ∧ (p4 ∨ p1)) → ((p3 ∧ (True ∧ p5)) ∨ ((p3 → (p3 → p4)) → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159035798172180695452234670421 : ((p4 ∨ (p5 ∨ ((p1 ∨ ((p3 ∧ p2) ∧ True)) ∨ ((p5 ∨ ((p1 ∨ (p3 → p4)) ∨ p5)) ∨ p1)))) ∨ (p3 → (((True ∨ p1) ∨ p2) ∨ p4))) := by
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
theorem thm_5_vars_219114057822540088327453626024 : ((True ∨ ((p4 ∨ p4) → p5)) → (((True ∧ ((True ∧ True) → ((((p2 → True) ∨ (p3 ∨ p4)) → (True → p3)) ∧ p2))) ∨ p5) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67397210232153521948253958102 : ((p1 → ((p1 → ((True ∧ (((False ∨ (p5 → ((p4 ∧ p1) ∨ (((p2 → p5) ∨ p3) ∨ p2)))) → (False ∧ False)) ∨ False)) ∧ False)) → p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50095607840059168149123339874 : (((p3 ∧ ((p5 ∧ ((p3 ∨ p3) → p3)) → (True ∧ ((((p1 ∧ False) ∨ (False ∧ False)) → p1) → p2)))) ∧ ((True ∨ (p3 → p1)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228723834688883058900641063803 : ((p2 ∨ (p1 → p2)) ∨ ((p4 → (((p2 → (p5 ∨ p1)) ∧ ((p2 → False) → p5)) ∨ (((((p2 ∧ True) → p3) ∨ p3) ∨ p5) ∨ p4))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721102517822263903651199472955 : (((((p2 ∨ p5) ∨ (p2 ∨ p5)) → (True → (((p3 ∧ (((False ∧ (((True → p4) → True) → p4)) → p5) ∨ p1)) ∨ (p2 ∨ p1)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54442388982222899062649585852 : (((((((p2 → p1) ∧ p1) → p4) ∧ p3) → p2) ∨ ((p4 ∨ (p1 ∨ (True → (False ∨ p5)))) ∧ (False ∨ (p1 → ((False ∧ p1) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243278169582298120909167042857 : ((p4 → p4) ∧ (((p2 → (((p3 ∨ (False ∨ (p3 ∧ True))) ∨ ((False → (p4 ∨ True)) → p1)) ∨ ((p3 → p1) ∧ False))) → (p2 ∨ p5)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214668476946844508420944933311 : (((p4 → False) ∧ (False → p3)) ∨ ((False ∨ (p1 ∨ p1)) → ((((((False ∧ False) → (False → (p1 → p5))) ∧ p4) → (p3 ∨ True)) ∧ p5) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_113576458349717147389268233897 : (((False ∧ ((False ∧ ((((True → p5) → (p4 ∧ (p4 ∧ (p4 ∨ (p2 ∨ p4))))) → (p3 → p3)) ∨ p4)) ∧ False)) ∨ (p3 ∧ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262139818918037329402410087520 : (True ∧ ((((((((p2 ∧ p4) → (p4 ∧ ((p4 ∨ ((p2 → True) → False)) → p4))) → (p2 ∧ (False ∧ p3))) ∨ p2) ∧ p1) ∨ True) ∨ p4) ∨ p2)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115163486910050124960548813756 : (((((p5 ∧ p3) ∨ ((p2 ∨ (p5 ∨ p1)) → p2)) ∧ p3) ∧ (((True ∨ p5) ∧ p2) ∨ ((p4 ∨ False) ∧ (False ∧ (p1 → True))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156930625392396636430945009389 : ((((((p3 ∨ (((p5 ∧ p2) ∧ (p3 ∧ p1)) → p5)) → (p4 → False)) → p1) ∧ (p2 → p1)) ∨ p2) ∨ (p2 → ((p2 ∧ (True ∨ False)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327112132700463170948326883206 : (True → (((True → p4) ∨ (((False → (p3 ∧ ((p5 → ((p2 → p5) → p5)) → p2))) ∨ (p1 → p3)) → (p3 ∨ (p1 → (p2 ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56196181880814303326271266846 : (((p5 ∧ (p5 ∨ (p1 → p4))) ∨ ((((p4 → True) → ((((p1 ∧ p4) ∧ True) ∨ (True → p4)) ∨ True)) ∧ (p3 ∨ (p5 ∨ True))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204417662645789249251313837245 : (((p4 → ((p1 ∨ p3) ∨ p3)) ∧ p2) ∨ ((True → p4) → (p5 ∨ (((p1 ∨ p4) ∨ (p3 ∨ (p2 ∧ ((p4 ∧ (p4 → p2)) → p3)))) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111047592035045559835861004533 : ((((p1 → (p4 ∨ (((p4 ∨ p1) ∧ ((p2 ∨ p1) ∧ False)) ∨ ((False ∨ p5) ∧ False)))) ∨ (((True ∨ False) → False) → p2)) ∧ True) ∨ (p2 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110781071149070979091389538535 : (((((((False ∧ ((p3 ∧ (p2 → p5)) ∨ ((p4 ∧ (p4 → (p3 → p5))) → (p2 → p3)))) ∨ p3) ∨ True) ∨ p3) ∨ p2) ∧ p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113885095639190159255632620256 : (((((((((((p4 → p5) ∨ ((False → p2) ∧ p5)) ∨ p3) ∧ p5) ∧ True) ∨ False) → p5) → p2) ∨ p2) ∧ ((False ∨ p1) ∨ p4)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693832866778848105650992168756 : ((((((p3 ∧ (p1 → False)) ∧ ((p5 ∧ (True ∨ (p3 → p2))) ∨ p5)) → p1) ∨ (p5 → ((p1 → p5) ∨ (((p5 ∧ p1) → p4) → p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179982229831600688023055238687 : ((((((p4 ∧ p2) → False) ∨ p2) → (False → (p3 ∧ (p5 ∧ p2)))) ∨ p4) → (p4 ∨ ((((True → p5) → p3) → (p5 ∧ p4)) ∨ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638845891947857326485012284906 : ((((((p2 ∧ (p2 → False)) ∨ p5) ∧ ((p3 ∨ (p5 → ((p4 → (p4 → (p5 ∧ False))) ∧ True))) ∨ (True → ((p3 ∨ p5) ∨ False)))) → p5) ∨ p3) ∧ True) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h9 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h10 := h6 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h12 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h13 := h6 h12
        -- False on the left can always be used.
        apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h15
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41964379632880365025427163906 : ((((p5 ∧ p4) ∧ (((p4 ∨ False) ∨ p5) → ((p2 → (p5 ∨ p3)) ∨ ((((False ∧ ((p4 → p2) ∨ False)) → p3) ∨ p1) ∧ p1)))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116866480099263135956379043119 : (((p1 → p5) ∨ ((p1 ∨ (((p2 → ((p2 → ((p2 ∨ True) ∨ p2)) ∨ p2)) ∧ ((p4 → p1) → (False ∨ p4))) ∧ p2)) ∨ True)) ∨ (True → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300566207668344516284893901282 : (False ∨ ((p2 ∧ ((p4 → (p1 ∧ (((((p2 ∧ p1) → True) → p2) → p3) ∧ (p2 → p5)))) → (p5 ∧ False))) ∨ ((p5 → p2) → (p1 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336450634098592129509179849456 : (p1 → ((p5 ∨ (p4 ∨ (p1 → ((True ∧ p2) ∨ ((p5 ∧ (True → ((p1 → p3) ∧ (p5 ∨ (False ∧ (p3 ∧ (p4 ∧ p5))))))) ∧ p2))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186625646093144092894291531078 : (((False ∧ ((p4 → False) → ((p4 → p1) ∨ p3))) → (p5 → True)) → ((p3 ∨ (False ∨ (False ∨ (True → p5)))) ∨ (((False ∧ p5) → p4) ∨ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355527205093006743116921361061 : (p5 → (((((p3 ∨ ((p5 ∧ (((True ∧ (p1 → (((p5 → p4) → p3) → p4))) ∨ p5) ∧ p3)) → p1)) ∨ p2) ∨ p2) ∧ True) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261639936695059695406751983099 : ((p5 → p5) → ((True → ((False ∨ False) ∨ (False ∧ (p2 → ((p3 ∨ (p5 ∧ p1)) → True))))) → (True → ((p4 ∧ ((True ∧ p2) ∨ p5)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104591576342420274825322005771 : ((((((p4 ∧ False) → (((p4 ∨ True) ∨ p4) ∧ p2)) ∧ p1) ∨ ((p5 ∨ (((p3 ∨ False) ∧ p1) ∨ False)) ∧ False)) ∨ (False → p1)) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181128729452437863709233324111 : ((True ∧ (p5 ∧ ((True ∨ (True → ((p5 ∧ p5) → (p4 ∨ p2)))) → p1))) → ((p5 ∧ ((p4 ∨ (p1 ∨ p5)) → (p2 ∧ p3))) → (p2 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : (p4 ∨ (p1 ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h10 := h4 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h18 : (True ∨ (True → ((p5 ∧ p5) → (p4 ∨ p2)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h19 := h17 h18
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39717837003225737488484395603 : (((p5 ∨ ((((p1 → ((False ∨ p3) ∧ (((p3 ∧ ((p1 ∨ p2) ∨ p4)) ∧ p5) ∧ p2))) ∨ (p3 → p4)) ∧ p5) ∧ (False ∨ p1))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



