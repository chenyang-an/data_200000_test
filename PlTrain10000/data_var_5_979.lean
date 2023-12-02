variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255266095512994250692670145307 : ((p4 ∧ p5) → (((True ∧ (p5 ∨ (True ∨ True))) ∧ (p5 → p5)) ∧ ((((p1 ∧ (((False → False) ∨ p5) → p1)) → (p2 ∨ False)) ∧ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254009613930664584408433227187 : ((p1 ∧ p5) → (False ∨ (((((p1 ∨ p4) ∧ (p4 ∨ (p4 → p2))) → False) ∧ (False → (p3 → p1))) → ((p1 → p3) ∨ (True ∨ (False ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152228668782212179296794886553 : (((p2 ∨ (p3 → (p4 → (p1 → p2)))) ∧ (True → ((False ∧ (((False ∨ (p3 ∨ p2)) → p5) ∨ p1)) ∧ p5))) → ((p4 ∨ p1) ∧ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
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
theorem thm_5_vars_248316763804234452385266472180 : ((p2 ∨ p3) ∨ ((((p2 ∨ (p4 ∧ ((p4 → p2) → (p3 → ((((p4 → p1) → (p1 → True)) → (False ∨ False)) ∧ False))))) ∧ True) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656456335829130402813141316555 : (((((((True → False) ∧ p1) ∨ ((p4 ∨ (p2 ∧ p4)) ∧ True)) ∨ (p1 ∨ ((True ∧ False) ∧ (((True ∧ p4) ∨ p3) → p1)))) ∨ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199388623700876000010270956136 : ((((p1 ∨ (p4 ∧ p2)) → (p2 → p3)) ∨ p5) → (((p1 → p5) ∧ p5) → (p5 ∧ ((((p5 ∧ (False → (p5 → p2))) ∧ True) → p2) ∨ p5)))) := by
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
  cases h1
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354611999394088644485572605854 : (p5 → ((((((p5 ∨ (p2 ∨ ((False ∧ p3) → p2))) → (False ∧ (p1 ∨ False))) ∧ ((False ∨ p4) ∨ p3)) ∨ (p2 → (p2 → p2))) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590105170046490725985412391638 : (((((((((p3 ∧ (p4 → True)) → p2) ∨ False) → (p3 ∧ p3)) ∨ ((((p2 ∧ (True ∨ p5)) ∧ (p5 ∨ p4)) ∧ False) ∨ p1)) → p3) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307750101066305958293652914007 : (p1 ∨ (p3 → (((p4 ∨ (p1 ∧ p2)) → ((p1 → (False ∧ (p1 ∧ False))) ∧ p4)) → ((p2 ∨ (((False ∨ p5) ∧ p3) ∧ p4)) ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318611604254049206312402213179 : (p4 ∨ (((True ∨ ((p5 ∧ p4) ∨ False)) → (((p3 ∨ ((p2 → (p2 ∨ ((p4 → p1) ∨ False))) ∧ (True ∧ p5))) → p1) ∧ p3)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215593148566726082374467046788 : ((p5 ∧ (False ∨ (True ∧ p4))) ∨ ((p4 → ((p3 → p2) ∧ (p3 ∨ (((p1 ∨ p5) → (((p3 ∧ False) ∨ p2) ∧ p2)) ∨ (False ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253856543097673400584148477399 : ((p1 ∧ p3) → ((((((((p3 ∨ p5) ∨ True) ∨ p5) ∧ ((p4 → p3) → p5)) ∨ (p5 ∨ p2)) ∨ True) ∨ ((p3 ∧ p2) → True)) ∨ (p2 ∨ True))) := by
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
theorem thm_5_vars_177233279894070029631108685508 : ((True ∨ ((p3 → p4) ∧ (True ∧ (((False ∨ (p2 ∨ True)) ∨ p5) ∨ True)))) ∧ ((p4 → (((True ∨ p4) ∨ (p3 → p1)) → False)) ∨ (True ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118590421797894653556983988384 : ((p4 ∨ ((True ∧ (p4 ∨ (p3 ∧ ((p4 ∨ ((p1 → (False ∨ ((p1 → p3) ∧ p1))) → p5)) → (p4 → (p1 → p3)))))) → p2)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238056318861396199707033141980 : ((True ∨ p2) ∧ (((p1 ∨ (((p2 ∧ (False ∨ p2)) ∨ True) ∧ p2)) ∧ (p5 ∨ ((p5 ∧ ((p3 → p4) → p4)) ∨ ((True ∧ p2) ∨ False)))) ∨ True)) := by
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
theorem thm_5_vars_351716908965181275549145256351 : (p4 → ((p5 → (((p3 ∨ (p1 ∧ (p3 → p4))) ∨ p4) ∧ (p3 ∨ (p4 ∧ p4)))) ∧ (p3 → ((p5 → p3) ∧ (((p3 ∧ p2) ∧ p1) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777334690537287369277292288451 : (((p1 ∨ ((((False ∨ ((True ∧ p3) ∨ p1)) ∨ ((p2 ∨ (p5 → (p4 ∧ p2))) → False)) ∧ (False ∨ p2)) ∨ (p3 ∨ ((False ∧ False) → False)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752849692481575111333900073448 : (((False ∧ ((p5 → (p2 ∨ (((((p1 ∧ (p1 ∨ p5)) ∨ False) → ((p2 ∧ True) → False)) ∨ (p1 → (False → (True ∨ p1)))) → p1))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714589381062737071444582185625 : (((((p2 ∨ True) ∨ ((p3 → False) → p4)) → ((((p5 → (p1 → ((True ∨ (p2 ∨ ((False ∧ p5) → p3))) → p3))) ∧ p4) ∨ p4) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137075060047154208320290876780 : (((p5 → True) → (((p2 ∨ p3) → ((((p2 → p3) → p2) ∨ True) ∧ False)) ∨ ((p3 → p5) ∧ (p5 ∨ (False → p5))))) ∨ (p4 → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60696010682844747196179354636 : ((True ∧ ((((False ∧ (p5 ∨ p2)) ∧ (p4 ∨ (p4 ∧ p5))) ∨ True) ∨ (True ∧ (((p5 ∨ (True ∨ False)) ∧ (p5 ∧ (p4 ∧ p1))) ∧ p3)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_777416485027849384481730647184 : (((p1 ∨ ((((False ∧ (p4 ∧ (p4 → p3))) ∧ (False ∨ ((p2 ∧ p1) → (p4 ∧ True)))) ∨ p2) ∨ (((p4 ∨ True) ∧ (True ∧ False)) → True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83291737089378493252312308381 : ((((((False ∧ ((p4 ∨ p3) ∨ False)) → (p2 → (True ∧ True))) ∨ p2) → ((p3 ∨ p5) ∧ p3)) ∧ ((True → p3) → (p2 → (False ∧ p5)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∧ ((p4 ∨ p3) ∨ False)) → (p2 → (True ∧ True))) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114268994919614973428449857185 : ((((False ∧ ((False ∨ (p1 → (True → True))) ∧ (p1 ∨ ((p4 ∨ False) → (p1 ∨ True))))) ∧ p5) ∧ (False ∨ (p3 ∧ (True → p3)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51032840492180964292503835431 : (((p5 ∧ ((p3 ∨ p4) → (((p3 → ((p1 ∨ p5) → p4)) ∧ (p5 → p3)) ∧ (p2 ∧ p3)))) ∧ (((p1 ∧ p4) ∧ p1) ∧ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50724948189271354362676775169 : ((((p2 ∨ p4) → ((((p2 ∧ False) ∨ (p2 → False)) ∨ (((p1 → p5) ∧ (p5 ∧ p2)) ∨ p3)) ∧ p1)) → (True ∧ ((p4 → False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27467033537216855244083953917 : (((p3 ∧ p2) → ((((True → False) ∨ (p5 ∨ ((((p4 → p2) ∧ (True ∨ ((p5 ∧ p2) → p5))) ∧ (True → False)) ∨ p5))) → p4) ∨ p2)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306012618250281768945518506463 : (p1 ∨ ((p3 ∧ ((p3 ∧ p4) → True)) ∨ (p3 → (p5 ∨ (False ∨ ((((p5 ∨ (((p3 ∧ p1) → (p4 ∨ p3)) → True)) ∨ p3) ∨ p1) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752702956638287138967151787573 : (((False ∧ ((((False ∨ (((p3 ∨ (p3 → True)) ∧ (p1 → p2)) ∧ False)) ∨ True) ∧ (False ∨ ((p4 ∨ ((False ∨ p3) ∨ p5)) ∧ p3))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59584229084458291174787791721 : (((p4 → False) ∨ ((p4 ∧ p2) → ((False ∧ p3) ∨ ((((p4 ∧ p4) → (p4 → (True ∧ (False ∨ (False ∨ p3))))) ∧ p4) → (p3 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323659726532282926066807025053 : (p5 ∨ ((((p5 ∨ (p3 ∨ ((((p3 ∧ (True → p5)) → False) ∨ p4) → p1))) ∨ (p3 ∧ p5)) ∧ (p3 ∧ False)) ∨ ((False ∨ True) ∨ (p4 ∧ False)))) := by
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
theorem thm_5_vars_114088074690868315136909117814 : ((((p5 ∧ True) ∨ (((p4 ∨ p5) → ((p2 ∨ p5) → p5)) → (p2 ∨ (p4 → ((p1 ∨ True) ∧ p2))))) ∨ (p2 ∧ (p4 ∧ p1))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626377370326475187959421852060 : ((((p3 → (p1 → (((p2 → p5) → ((False ∨ p5) → ((p5 ∧ (((p1 ∨ True) ∨ (p4 ∧ p3)) ∨ p4)) ∧ p2))) → (p2 ∧ False)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_193598080853997612538696496067 : (((p3 → True) → (True ∧ (False ∧ ((p2 → True) ∧ p4)))) → ((p5 ∧ p3) ∨ ((p1 ∧ (((p5 ∨ (p2 → p5)) ∧ p5) ∨ (True ∧ False))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355001123303629451251286226506 : (p5 → ((((((((p1 ∨ (True ∨ (False ∧ p3))) ∨ p1) → False) ∨ True) → p4) ∧ ((p4 → p3) → (p1 ∧ (p5 ∨ (p4 ∨ p1))))) ∧ p5) → p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : ((((p1 ∨ (True ∨ (False ∧ p3))) ∨ p1) → False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148040055978743532807277292532 : ((((p5 ∧ p5) → ((p1 ∨ (False → p4)) → (p2 → ((p1 ∧ p5) ∨ (p3 ∧ (p4 ∨ True)))))) ∨ (False → p3)) ∨ ((p1 → (p1 ∧ p2)) ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116400752786032823372094637163 : (((p4 ∧ (p2 ∨ p5)) → ((p3 ∨ (p1 ∧ ((p3 → (p2 ∧ (((p1 → (p4 ∨ True)) ∧ p1) → False))) ∧ (p1 ∨ p1)))) → False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_104564243163752687808641726385 : (((((True → ((p3 ∧ ((((p5 ∨ p1) → p5) → True) ∧ (p3 → p2))) → p4)) ∧ p5) ∧ (p2 ∨ (p1 ∨ p3))) ∨ (False → True)) ∧ (p2 → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336953117253135257833694750166 : (p1 → (((((p4 ∧ p2) ∨ ((p4 → ((p4 ∧ (False ∧ p3)) ∨ (p4 ∧ False))) ∨ p1)) ∨ ((p3 → p3) → p5)) ∨ (True ∧ p5)) ∧ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655952101899606589071897178521 : (((((p5 ∧ (False ∧ (p4 → (p1 → (((p2 ∧ ((p2 ∨ p5) ∨ True)) ∨ p3) ∧ p5))))) ∧ (((p3 ∧ p4) ∨ False) ∨ p1)) ∨ (p4 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767821314229163486023515920472 : (((p5 ∧ ((((True → (True ∧ (((p2 ∧ p3) ∨ (p4 ∨ ((True → (False ∧ p5)) ∧ p3))) ∨ (True ∨ p3)))) ∧ False) → (p4 → p5)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190333891576146711338756836245 : ((((p2 ∨ (p2 ∨ (p5 → p4))) → (p4 → p5)) ∨ True) ∨ ((p5 ∨ (p2 ∨ p5)) ∨ (p2 → (((p4 → True) ∧ True) ∧ (p4 → (False ∨ p2)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199683607490633350444008624316 : ((((False ∨ p1) → ((p5 ∧ p2) → p1)) → False) → (p2 ∨ (p5 ∨ (((((p1 ∧ p3) → (((False → False) ∨ p5) ∨ p5)) ∧ p2) ∨ True) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∨ p1) → ((p5 ∧ p2) → p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217115890672470949587623027798 : ((((p1 ∨ p5) ∨ p2) ∨ p4) → (((True ∧ p3) ∧ (True ∧ (((p1 ∨ ((p2 → p3) ∨ (p2 → False))) ∧ p3) ∧ (True ∧ True)))) ∨ (p5 ∨ True))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205247137309604343855668262559 : ((((p3 ∨ p1) ∨ p3) ∨ (p2 → p1)) ∨ (p1 → (False ∨ (((((p3 ∨ ((False ∧ p3) ∧ True)) ∨ p3) ∧ (p2 ∧ (True ∧ False))) ∨ p4) ∨ True)))) := by
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
theorem thm_5_vars_52209764377890252458808858802 : ((((False ∧ p5) ∨ (((p2 ∨ False) ∧ (p1 ∨ p4)) ∧ (p2 ∨ ((p2 → True) → p1)))) → (p3 ∧ ((p2 → p1) ∧ (p5 ∨ (False → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775367702137133641632069618176 : (((False ∨ (p1 ∧ ((False ∨ (((p3 → (p3 ∧ p3)) ∨ (p3 ∨ (True ∨ (p4 → (False → (((p3 ∧ p3) ∧ p4) ∧ p1)))))) ∧ p2)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792379526956539130858370218433 : (((True → (((p2 ∨ False) → (((p3 → (False ∨ p1)) ∧ p2) ∧ ((p1 ∨ p4) ∨ p3))) ∨ (p5 ∧ ((p3 ∨ (p5 ∨ (p1 → p2))) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307203185837265083829136092694 : (p1 ∨ (p1 ∨ ((p4 ∧ (p1 ∨ (p4 ∨ ((p1 → p1) ∨ (p5 → (False → False)))))) ∨ (False → (((p2 ∨ p5) → (True ∧ (True ∧ p3))) ∧ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107621133419282434655072201280 : (((p1 ∨ True) ∧ (((((True ∨ p5) → p5) ∧ p5) → (p4 ∨ ((((p4 → (False → (False → p4))) → p1) ∧ p5) ∨ True))) ∨ p1)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191226514615541245464166574426 : (((p3 ∨ (p4 ∧ True)) → (p3 ∧ (p2 ∨ (False ∨ False)))) ∨ (True ∨ (((p2 → p3) ∨ ((p3 ∨ (True → p1)) ∨ (p3 → p2))) ∧ (p2 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213561674257255062788588632358 : ((((False ∨ p2) ∧ p1) ∨ p1) ∨ ((p4 → (p4 ∧ (p1 ∨ ((p4 ∧ p5) ∧ (True ∨ p5))))) ∨ (p1 → ((False ∨ p1) ∧ (False → (False ∧ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177905532316193777376182896432 : ((((p4 → (((p5 ∨ True) → (False ∨ False)) ∧ False)) ∨ (False → True)) ∨ p2) ∨ ((p2 ∧ p1) → (p1 ∨ ((False ∧ (p3 → p3)) → (True → p3))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50791629176920011435838588727 : (((p5 ∨ (p5 → (((p2 ∧ p1) → p4) ∧ (((p1 ∨ False) → p3) ∨ (p1 ∨ ((p5 → p1) ∨ p5)))))) → (p2 ∨ (p3 ∨ (False ∨ True)))) ∨ p4) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712577411850309806366225716049 : ((((((p1 ∨ p3) → False) → (p4 → p3)) ∨ (p2 → ((((p3 ∨ (p3 ∨ (((p4 ∧ p1) ∧ p3) ∧ (p2 ∨ p1)))) ∨ False) ∨ p3) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46066099363175149469318231579 : ((((((p3 ∧ (p3 ∧ ((((p3 → (p5 ∨ p2)) ∨ True) ∧ (p4 ∧ (False ∧ p3))) ∨ (True → p3)))) ∨ p5) → p2) ∨ p1) ∧ (p3 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624723379164603679259298040776 : ((((p4 ∨ (p1 → (((((p3 ∨ True) ∨ ((p1 ∧ False) → p4)) ∨ (p1 → True)) → (((p3 → p2) → p4) ∨ (True ∧ p4))) ∨ p4))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2451753909557191426289384772 : ((((p3 ∨ (p5 → False)) ∨ ((False → True) → p1)) ∨ p2) ∨ ((((False → p2) → (p4 ∧ p1)) ∧ p5) ∨ (p2 ∨ (p1 → (p3 ∨ True))))) := by
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
theorem thm_5_vars_42503377113824617425661056097 : (((False ∨ ((((False → p5) ∧ ((True ∨ p2) ∨ ((p1 → True) ∨ (True → True)))) → False) ∨ ((p4 ∧ p1) → ((p3 → False) → p3)))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248154101693750081735969832363 : ((p2 ∨ False) ∨ (((p4 ∨ (((False ∨ ((True ∧ p1) ∧ p3)) ∧ p5) ∧ p5)) → (p2 → ((p4 ∨ False) ∧ True))) ∨ ((True → p3) ∨ (p2 → True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340982284020141564087192787962 : (p2 → (((p1 → p3) ∨ (p5 ∨ (p4 ∧ (p4 → ((p4 ∧ (p3 → (p4 → ((((p3 ∧ p3) ∧ p1) ∧ True) → p5)))) ∨ (p5 → p5)))))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304725155584507122885838350515 : (p1 ∨ (((((p4 ∨ ((p2 → p1) ∧ (((p5 ∨ p3) ∧ p1) ∧ p3))) ∨ p3) ∧ p1) ∨ ((False → (p2 → (True ∧ p4))) ∨ p5)) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157113702311073071897664573781 : (((p5 → (True ∧ ((p5 ∧ (p3 ∧ ((p1 ∨ (False → p2)) ∧ p5))) ∧ ((True ∧ False) ∧ p2)))) ∨ False) ∨ ((p1 ∧ p3) ∨ ((False ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112043941952126398592157940031 : (((((True ∧ p3) → p1) → (((True → p2) ∨ ((True ∧ (p1 ∧ (p2 → ((p4 ∨ p1) → (p3 → p4))))) ∨ True)) ∨ True)) ∨ p3) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44013599835008022995489391518 : (((((((((p1 ∨ False) → p1) → p5) → (p5 → p1)) ∧ (p1 → p2)) ∨ (p1 ∨ (False → ((p5 ∨ False) ∧ False)))) → (p4 ∧ p4)) → p4) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p1 ∨ False) → p1) → p5) → (p5 → p1)) ∧ (p1 → p2)) ∨ (p1 ∨ (False → ((p5 ∨ False) ∧ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111785462104251222793761157924 : (((((((p4 ∧ p2) → p3) ∧ ((p4 → (p1 ∧ (p2 → False))) → False)) → ((p5 → (False ∨ True)) → False)) ∨ (p3 → p3)) ∨ p1) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637799557146041490596083280054 : (((((p5 → ((((p5 ∧ p4) ∧ p5) ∧ (p5 → True)) ∧ p5)) → ((p1 ∨ ((False ∨ (p2 ∨ p1)) ∧ (p4 ∨ False))) ∧ (True ∧ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198959402539906141180931912646 : ((p4 → (p1 → ((p4 ∧ False) ∨ (False ∧ p3)))) ∨ ((True ∨ (p3 ∧ (True ∧ False))) → (p5 ∨ (p4 ∨ (((p5 → p4) → p4) ∨ (False → p1)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50140538041063480053966919318 : (((True → ((p2 ∨ p4) ∨ (((p3 → (True ∨ (p1 ∧ ((True ∨ p4) ∧ True)))) ∧ (p4 → p1)) ∧ True))) ∧ (((p5 ∧ p2) ∧ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328888615811010675390216751841 : (True → (((p1 ∨ (False ∧ False)) ∨ (p1 ∧ (False → True))) ∨ ((((((p4 ∨ (p2 → True)) ∨ False) ∨ p3) → ((True ∧ p1) ∧ p5)) ∨ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37325489003016239400193112091 : (((((((p3 ∧ p4) ∨ ((((p5 ∧ (((False ∨ p5) → (p2 ∧ p3)) → p4)) ∧ (p5 ∧ p5)) ∨ False) ∨ p3)) ∨ p5) ∧ p5) ∨ p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127642733864424391604328387559 : ((p5 ∨ (((True → (p3 → ((((((p5 → p4) ∨ p1) → (False ∧ p3)) ∧ (p5 → p3)) ∨ p4) ∧ p4))) → True) ∨ (p4 ∧ True))) → (p4 → p4)) := by
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
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354625157851394457153050453192 : (p5 → ((((p1 → p2) → ((((((p3 → ((p3 → p2) ∨ False)) → p5) → p3) → (p3 ∨ (p2 → False))) → (p3 ∨ False)) ∧ p3)) ∨ p2) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329507437001703167662419494663 : (True → ((True ∧ False) ∨ (p4 → (False ∨ ((((p5 ∨ (True → False)) ∨ p5) ∧ (False → (True ∧ (True ∧ False)))) → ((p5 ∧ (True ∧ False)) ∨ True)))))) := by
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
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
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
theorem thm_5_vars_760174771211793588051411004484 : (((p2 ∧ ((False ∧ p4) ∧ ((p2 → ((p5 ∧ (p4 ∧ p1)) ∨ (p5 ∧ ((p5 ∧ ((True ∧ p4) ∧ p4)) ∧ ((True ∨ p2) → True))))) ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59674787361637370507666192391 : (((True ∧ p2) → (p5 ∧ (((True ∨ p1) → ((((p1 ∨ True) ∧ (p1 ∧ p5)) → p3) → ((p1 → p5) ∨ p4))) ∨ ((p4 ∨ p1) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160497481213366410570340784387 : (((((p2 → (p4 → p3)) → ((p5 ∧ p3) → p2)) → (p5 ∧ p4)) ∧ ((True ∨ (p2 ∨ p4)) ∧ p5)) → (((p5 ∨ p3) → False) → (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48194302351858070625402253866 : ((((False → p4) ∨ (((((False → (((p5 ∨ (p4 ∨ p5)) ∧ p2) → p2)) ∨ p5) ∨ p4) → True) → (p5 ∧ (p1 → p5)))) → (p3 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112555558396500192330472841571 : (((((p2 ∨ p1) ∨ ((((p2 ∨ (p2 → p4)) → (p3 ∨ p4)) ∨ (p5 ∨ True)) ∧ (p1 ∨ ((p4 ∧ True) ∨ p1)))) → p4) → p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252754228451487582337163094015 : ((True ∧ True) → ((p1 ∧ ((p5 → (p2 → (p2 → (p1 ∨ p1)))) → (p4 → (False ∨ ((((p4 ∨ p3) ∧ p4) ∧ True) → (p3 → p1)))))) ∨ True)) := by
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
theorem thm_5_vars_169729026798406098518823344767 : (((p2 ∧ (p4 → ((p4 ∨ (p1 → False)) → ((p4 → (p4 → True)) ∧ p2)))) → True) ∧ ((((((p1 ∨ p2) ∨ p5) ∨ p5) ∨ False) ∨ True) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53382043467455552295719066346 : ((((((True ∨ p2) ∧ False) ∨ (True → (True → (p1 ∧ True)))) → False) → (((p4 → (p5 ∨ p3)) ∨ (((p2 ∧ p2) → False) ∧ False)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36244983709068538002390280041 : ((p4 → ((((p5 ∧ p3) → (p2 ∨ (p1 ∧ ((p5 ∨ (((p4 ∨ (((p2 ∨ False) ∧ p4) → p2)) ∧ p1) ∧ p4)) ∧ p2)))) → p5) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341697660119493636183427524084 : (p2 → ((((((False ∨ False) → p4) ∨ ((p2 ∧ p3) → p4)) ∧ (False ∨ ((((p3 → True) ∧ p1) ∨ True) ∧ p5))) → (False ∨ False)) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42020037574338166270461103528 : ((((True ∧ p5) ∨ ((p1 ∨ p2) ∨ ((p4 → p3) ∨ ((p4 → ((p4 ∧ ((p4 ∨ (p1 ∨ p1)) → (p2 ∧ p4))) ∨ p3)) ∨ p3)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51287683584341714197796760225 : (((p3 ∧ (True ∨ ((p5 ∧ (p3 ∨ ((p2 ∧ p5) → (p4 ∨ (p1 ∧ False))))) → (p3 → False)))) ∨ ((p1 ∨ p1) → (p3 ∨ (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57304534707954903728096148572 : ((((p5 → p3) → p2) ∨ (((((False → p4) ∧ True) → (p3 → p1)) → (p5 ∧ (False ∧ True))) ∧ (((p3 ∨ p1) → (False → True)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666254974307059522521221693755 : (((((((((p5 ∨ (p4 → (p4 ∨ (False → (False ∨ p4))))) ∨ p3) ∨ False) ∨ p4) → (p4 ∧ True)) → (False ∨ p5)) ∧ (True → (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350835149594556842522609668286 : (p4 → (((p4 → ((p2 ∨ p5) → ((((p2 ∧ p3) ∧ (p3 ∨ p4)) ∨ p5) ∧ (p3 ∨ p5)))) ∨ (((p5 ∧ p5) ∧ p1) → p4)) ∧ (p4 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1812173371113985647720505642 : ((False ∨ ((((p3 ∨ True) → ((p3 ∨ (p4 ∧ False)) → False)) ∨ (p5 ∧ (p3 → True))) → (p1 ∧ (p3 ∧ p3)))) ∨ (p1 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47279904614141729715594685533 : ((((p1 ∧ ((p3 ∧ p3) ∨ False)) ∨ ((((p5 ∨ p2) ∨ p4) ∧ p2) ∨ ((((p5 ∨ False) ∧ (False ∨ p1)) ∨ p2) ∧ p3))) ∨ (p1 ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50229693297277968100015954935 : ((((p2 → (p1 → (p4 ∨ ((((p3 ∧ p3) ∨ (p1 ∧ p4)) ∨ (p2 ∧ (p5 ∨ p3))) ∨ p3)))) ∨ p4) ∨ ((p1 → (p3 ∧ False)) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111916893505382393872875238903 : (((((False ∧ p3) ∨ (p5 ∨ (p3 ∨ (((False → p1) ∧ p2) ∨ p3)))) ∨ (p2 ∧ ((True ∧ (False ∨ p4)) ∧ (True → p5)))) ∨ True) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51285568971702189898454804739 : (((p3 ∧ (((p2 ∧ ((False ∧ p1) ∨ ((p4 → (p4 ∧ (p3 ∧ p4))) → p1))) → False) → False)) ∨ ((p3 ∧ (p1 → False)) ∧ (True → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65627157629577009091722050764 : ((p4 ∨ (((p3 ∧ (((p1 ∨ ((True ∧ (True → (p5 ∨ ((p1 → p3) ∧ (False ∨ p2))))) ∧ p2)) → (p3 ∧ p5)) ∨ p5)) ∨ True) ∨ p5)) ∨ p4) := by
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
theorem thm_5_vars_613917026991145438388925070547 : (((((((((p5 ∨ (p5 ∧ (False → p4))) ∨ ((p5 → p2) ∨ p2)) → p4) → (p2 ∧ False)) ∧ (p1 ∧ p3)) ∨ (True ∨ (p2 ∨ p2))) ∨ p2) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_345625911076539881369564293658 : (p3 → ((False ∧ (((p5 ∨ True) → ((((p5 ∨ (p5 ∧ p4)) ∧ p4) ∧ ((p3 ∨ True) ∨ p4)) ∨ (True ∧ (True ∧ p2)))) ∧ (p3 ∨ p3))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227547248640375133740476544258 : ((True ∧ (p2 → False)) ∨ ((((p3 → p3) ∧ ((False ∨ p1) ∨ p1)) ∨ (p4 ∧ p3)) ∨ (p3 ∨ (p3 → ((p2 → (p2 ∨ p1)) → (p4 → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230429223271778610002492581397 : (((p4 ∨ p3) ∧ p4) → (((p5 ∧ p4) ∨ ((p2 ∨ ((((False → (p3 ∧ True)) ∧ p3) → p3) ∧ ((False ∨ (p4 ∨ p5)) ∧ p3))) → p2)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217811990216466593797363777098 : (((p2 ∨ (p1 ∨ p5)) → False) → (((p3 → ((p3 ∨ True) → (p4 → True))) → ((p4 → p2) ∧ (((True ∧ True) → p4) ∧ p3))) → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 → ((p3 ∨ True) → (p4 → True))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9



