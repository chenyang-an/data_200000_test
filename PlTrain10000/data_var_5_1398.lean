variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147449843580888437745936491494 : ((((True → p4) ∨ (p5 ∧ ((True → ((p4 ∨ False) → p5)) ∧ (((p4 ∧ p4) ∧ False) ∨ (p1 ∧ True))))) ∨ False) ∨ (True ∨ ((p3 ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149853559981326977991515139566 : ((p1 ∨ (p4 ∨ (p5 → (p5 → (((p3 ∧ True) ∧ (((p3 ∨ p2) → p4) → ((p2 ∨ p3) ∨ p4))) ∨ p5))))) ∨ ((p1 ∨ True) → (p3 ∧ p5))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257212895288854154685271568776 : ((p2 ∨ p2) → (((p4 ∨ (False ∨ p1)) ∧ p1) ∨ ((((p4 → p4) → (False → ((p2 → (p1 ∧ (False → p2))) → p3))) → (False ∧ p4)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327834246600713355958808742621 : (True → (((((True ∨ (p4 ∧ (((False ∨ True) → True) → ((p5 ∨ False) ∨ p2)))) → p2) ∨ (p2 → p5)) → (False ∧ (p4 ∧ p5))) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60393914633232281082675573781 : (((p3 → p4) → ((p5 → p1) ∨ (((p3 ∨ False) ∧ ((p3 ∧ ((p2 ∨ False) ∧ False)) → p4)) ∨ (((p3 → p5) → False) ∨ (True ∨ p1))))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200599819047978990292106926906 : ((True ∧ (p1 ∨ (p3 → ((p1 ∧ True) ∨ p4)))) → ((((((p1 ∧ p4) ∧ p1) ∨ (((p1 ∧ False) ∧ False) ∨ (p5 ∨ p2))) ∨ p3) ∨ False) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47181800088475865228984591554 : ((((p5 ∧ ((p4 ∨ ((False → p2) → (p4 ∨ p1))) → (p1 → (p5 → p4)))) → (p3 → (((p1 → False) ∨ True) ∧ False))) ∨ (True ∧ True)) ∨ p5) := by
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
theorem thm_5_vars_166279134820400902770706487265 : ((p4 ∧ ((((((p2 ∨ p3) ∨ ((p5 ∧ p5) ∨ (p2 ∨ p1))) ∧ True) ∧ p1) ∧ p2) ∨ True)) ∨ (((True → (p5 → True)) ∨ p1) ∧ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224111374066298574103950421962 : ((p5 ∨ (False → False)) ∧ (((p5 ∨ (((((((p5 ∧ p2) ∧ p3) ∧ p1) → p5) → p3) ∧ ((p2 ∨ p4) ∧ p3)) → True)) → False) ∨ (True ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808017190080451409664183361350 : (((p4 → (True ∧ ((((p4 ∧ p1) → (p3 ∧ ((p3 ∧ (p2 ∧ p2)) ∨ ((False ∨ p5) ∧ True)))) → (p2 ∧ ((True ∨ p3) → True))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244328464151009703435707020544 : ((False ∧ False) ∨ ((p5 → (((((p2 ∨ False) ∧ False) ∧ ((p5 → (p4 ∧ (False → p2))) ∧ p5)) ∨ True) ∧ True)) ∨ ((False ∨ True) → (p5 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135038524045249826232558361900 : ((((False ∧ ((p3 ∨ ((p1 → p3) ∧ (((True → p1) ∧ p1) ∨ (False ∧ (p2 ∨ p3))))) ∨ p5)) ∧ p5) ∨ (True ∨ p2)) ∨ ((p3 ∧ p2) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185048056680797688799291492749 : (((p4 → p4) ∧ ((p1 ∨ p3) ∧ (False ∨ (p5 → (p5 ∨ p2))))) ∨ (p1 ∨ (p4 → (p4 → ((p2 ∨ (True ∧ (False → p2))) ∧ (True ∨ False)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245342747139554418613195570906 : ((p2 ∧ p3) ∨ ((((((p3 → (p5 ∨ (p1 → p5))) → (p3 → ((p3 → p1) → True))) → p2) ∨ (p5 → (p4 → True))) ∨ (False ∧ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_256667473028322923132810837751 : ((p1 ∨ False) → ((p1 → ((False → p4) ∧ p3)) → ((((p1 → (p5 ∨ (p3 ∨ p5))) ∨ ((False → p1) → p3)) ∧ (p3 → p5)) ∨ (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225092119687458458254498490412 : (((p2 ∧ True) ∧ p3) ∨ ((((((((((p2 → (p4 ∧ p3)) → p4) ∧ p5) ∨ p2) ∨ True) ∨ (p2 → p3)) ∨ (True → False)) ∨ p1) → p5) → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((((p2 → (p4 ∧ p3)) → p4) ∧ p5) ∨ p2) ∨ True) ∨ (p2 → p3)) ∨ (True → False)) ∨ p1) := by
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262330868035226833545846393509 : (True ∧ (((p3 ∨ ((p5 → p1) → (False ∧ p5))) ∧ ((False → p1) ∨ ((((False ∧ ((p2 ∧ (False ∧ False)) ∨ p4)) ∨ p5) ∨ p4) → p3))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349291620848760481119732436264 : (p3 → (p2 → (((p4 ∨ (((p1 → (p4 ∨ (p3 ∨ p5))) ∨ (True ∧ ((False ∧ p5) ∨ True))) → p1)) ∨ True) ∨ (p1 ∧ (p5 ∨ (p5 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234698913025886138965581495101 : ((p4 → (False ∨ True)) → (((p5 → p5) → (((p1 ∨ False) ∧ p1) ∧ (((False → p3) ∧ (True → p4)) → (False ∧ (False ∨ True))))) ∨ (True ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60244472979826021336357838917 : (((False → True) → ((((p3 ∧ True) ∧ ((p5 → (p2 → (p3 → False))) ∨ ((((False ∧ p2) ∨ p2) → p5) ∧ (p5 ∨ p3)))) → p2) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350143060741037587302399390179 : (p4 → ((((p4 → p1) ∧ ((p2 ∨ (((True → p2) ∧ p3) → p5)) → p4)) ∨ ((p3 → True) → (((p5 ∧ p4) ∧ p3) ∧ (p2 ∧ False)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47145119681916964565416468466 : ((((((p2 → (p2 → (p5 → (True ∨ (p5 ∧ (p2 ∧ False)))))) ∨ (p4 → p1)) → p5) ∨ ((p1 ∧ (False → True)) → p5)) ∨ (False → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257681099554164174052653965536 : ((p3 ∨ p3) → ((((p2 → ((False → (p5 → True)) ∧ (p1 → p1))) ∧ p2) ∨ ((p5 → False) → (p1 ∨ ((p5 ∨ p2) ∨ p3)))) ∧ (False ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346375496389330254650615289901 : (p3 → ((p5 ∧ (True ∧ (((True ∨ (p2 → p4)) → ((True ∨ p3) → p2)) ∨ ((True ∧ ((True → (True → p3)) → True)) → p5)))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51927951832243107850856349475 : (((((p5 ∨ (p5 → (p3 ∨ True))) → (p4 ∨ (False ∨ p2))) ∨ (True ∧ (False → p3))) ∨ (False ∧ (p3 ∨ (((p1 → p5) → p5) → False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111595515499242481861634027142 : ((((p2 → ((p1 ∧ (p5 ∧ ((p2 ∨ p4) ∧ (p2 ∧ (p1 ∧ (p4 ∨ (((True → p4) ∨ p1) → p3))))))) ∧ p5)) ∧ p2) ∨ p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115049507705131266398984557600 : (((((((p1 ∨ p2) → p3) → p4) → (p4 ∧ (p5 → p2))) → p4) ∨ (((p5 → p1) ∨ p3) ∨ (False ∨ ((p1 ∧ False) → p2)))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136878388567361251576892877197 : (((p1 ∨ p2) ∨ ((p3 ∧ ((True ∨ (p4 → ((p3 ∧ p1) ∧ p5))) → p4)) ∨ ((((True ∨ True) → True) ∨ True) ∧ True))) ∨ (p3 → (p1 → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_609736197919238943511608125896 : (((((p3 ∨ (p5 ∧ ((False ∨ (False ∧ (((p3 ∨ p2) ∧ True) → (True ∨ p4)))) ∧ (((p2 → p4) ∧ p5) ∧ (p5 ∧ p1))))) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_138220716030178910533885436521 : ((p2 → ((((True ∧ ((p2 ∨ p3) ∨ p4)) ∧ True) ∧ (((p3 ∧ p2) → False) ∨ ((p4 ∧ p4) ∧ (False → False)))) → p5)) ∨ ((p2 ∧ False) → p4)) := by
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
theorem thm_5_vars_191119977934452520838384004857 : (((p4 ∨ (p3 ∨ False)) ∧ (((p4 ∧ p3) ∧ p2) ∧ p4)) ∨ ((p4 → p4) ∨ ((p2 ∨ (p4 ∧ ((p5 → p2) ∨ p1))) ∧ ((p1 → False) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159301787832555334656433212842 : ((p5 → ((((p2 → ((p4 ∧ (False ∨ p3)) → (p1 → p4))) → ((p3 ∧ p4) → False)) ∨ p5) ∧ p3)) ∨ ((True → True) → (p1 → (False ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116287828152502543346726391747 : (((p3 ∨ (p4 ∧ p2)) ∨ (p2 ∧ (False ∧ (((((((True → (p4 ∧ True)) → p5) → p5) ∧ p3) ∨ p3) → p5) ∧ (p1 ∧ False))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191633384213987118192970546933 : ((p4 ∧ (((p1 ∨ ((p4 ∧ True) ∨ True)) → False) ∨ p3)) ∨ (((p5 → ((p5 ∨ (p4 → (True ∧ False))) ∧ p1)) ∧ (True ∧ p5)) → (p1 ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148612183118249223050692930682 : ((((p1 → ((False ∧ p5) ∧ ((p3 ∨ p5) → p4))) ∨ True) → (((False ∧ p5) ∨ p4) ∧ ((p1 ∧ False) ∨ p4))) ∨ ((p4 ∨ p3) → (p3 → p3))) := by
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
theorem thm_5_vars_115077355490763003362589215805 : (((True ∧ ((True ∨ (((p2 ∧ (p1 ∨ False)) ∧ p5) ∧ p5)) → False)) ∨ (p5 ∨ ((False ∧ p3) ∨ (((p5 → p1) ∧ p1) ∧ p5)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240869655783871716946525253259 : ((True → True) ∧ ((((p3 ∨ (((p1 → (True ∨ p3)) ∧ p2) ∧ True)) ∨ p4) ∧ (p5 ∨ False)) ∨ (p5 → ((((p4 ∨ p5) ∨ p1) → False) → p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ p5) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135870836454673225914037785942 : ((((p4 ∧ (False ∧ (p4 → True))) ∧ ((True ∨ False) ∧ (p4 → p2))) ∨ ((((True ∨ (p3 ∧ p4)) → p3) ∨ p1) ∧ p4)) ∨ (p5 → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356034306678085668669472355128 : (p5 → (((p2 ∧ (p5 ∨ (p2 ∨ p3))) → ((((p1 → p3) ∧ ((p2 → p5) ∨ p4)) ∧ (False ∧ p4)) ∨ p4)) ∨ ((False ∧ p2) ∨ (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200407133003690236113092211303 : (((p4 ∧ p2) ∨ (True ∧ (p2 → (p4 ∧ p3)))) → (((False → ((False ∧ (False ∧ False)) ∨ (p4 → False))) → (p3 ∧ p2)) → (p5 → (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : (False → ((False ∧ (False ∧ False)) ∨ (p4 → False))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h14 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h15 := h9 h14
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47800385574666255469613985919 : ((((((p3 → p4) → ((p1 ∧ (((p5 → p3) ∨ ((((True ∧ p3) ∧ p4) ∧ p4) ∧ p1)) ∨ False)) ∧ False)) → p5) → False) → (p3 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783296255705587212677960780636 : (((p3 ∨ (((False ∧ p2) ∧ ((False ∨ (((p5 → True) ∨ ((p1 ∧ p5) ∨ p5)) ∧ (True ∧ p2))) ∧ p1)) ∨ (p1 → ((p5 ∧ p4) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69263088649327446901511712569 : ((p5 → ((p5 ∨ p1) ∧ ((p1 ∨ ((((((p1 ∧ (True ∨ ((p1 ∨ p4) → p4))) ∧ True) → p3) ∧ p2) ∨ True) → (p2 ∧ p4))) ∨ True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306416691692321228778965928079 : (p1 ∨ ((p3 ∧ p3) ∨ ((((((False ∨ p5) ∧ p1) → ((False ∧ False) ∨ p5)) ∧ True) ∧ True) ∨ (((p2 ∧ p4) → (p4 ∨ p1)) → (False → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642990302063711277205531932224 : ((((p2 ∧ (((p1 ∨ True) → p4) → (((p4 ∨ (p4 → p5)) → ((False ∧ (p5 ∧ False)) ∨ ((p4 ∧ p5) ∨ p1))) ∧ (p2 → p2)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711746347618412196748059401839 : (((((((p2 → p4) ∧ p2) ∨ p2) ∧ False) ∨ ((p2 ∧ p3) ∨ (False ∨ (p2 ∧ ((p3 ∨ (p2 → ((p2 ∨ p4) ∨ p4))) → (p5 ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64860276374043883855403535716 : ((p2 ∨ ((((((p1 → (p2 ∧ (True ∧ (p2 ∧ ((p2 → p3) ∨ False))))) ∨ ((False → p1) ∨ p1)) ∧ p3) ∨ p2) ∧ True) ∨ (True ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931910844972106142748392737 : (((((((False → (p5 ∧ p2)) ∧ p1) → False) ∧ p1) ∧ ((((p4 → False) ∧ True) ∨ True) ∧ ((True → p1) ∨ (p4 ∨ p3)))) ∧ p2) → p4) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h13 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h14 : ((False → (p5 ∧ p2)) ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h15
        -- False on the left can always be used.
        apply False.elim h15
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h16 := h6 h14
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h20 : ((False → (p5 ∧ p2)) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h21
          -- False on the left can always be used.
          apply False.elim h21
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h22 := h6 h20
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h24 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h25 : ((False → (p5 ∧ p2)) ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h26
        -- False on the left can always be used.
        apply False.elim h26
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h27 := h6 h25
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h31 : ((False → (p5 ∧ p2)) ∧ p1) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h32
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- False on the left can always be used.
          apply False.elim h32
          -- False on the left can always be used.
          apply False.elim h32
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h33 := h6 h31
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114479422432863205332130453082 : ((((((False ∨ ((p2 ∧ p3) ∨ True)) ∨ ((False → True) → (p1 → False))) ∨ p1) ∨ (p3 ∨ True)) → (p5 ∨ ((p5 ∧ p2) → p2))) ∨ (p1 ∧ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
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
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- One of the premise coincides with the conclusion.
            exact h12
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- One of the premise coincides with the conclusion.
      exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- One of the premise coincides with the conclusion.
      exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58197010830114094764633200722 : (((p4 ∧ True) ∧ ((((p3 ∧ ((p2 ∧ (((True → (p4 ∨ p5)) → (p1 ∨ False)) → p4)) ∧ (p1 ∧ (p1 ∨ True)))) ∨ p5) ∧ p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193231798969191392826527077164 : ((((False ∨ p3) ∨ p3) ∧ (p5 ∨ (p4 ∨ (p4 → p3)))) → ((((p2 ∧ (p2 → (p3 → True))) ∧ p3) → (p3 ∧ False)) ∨ (p5 ∨ (False → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- False on the left can always be used.
          apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50677238819062413684235781539 : ((((p4 ∧ ((p1 ∨ True) ∧ p1)) ∧ ((p3 ∨ ((p3 ∧ True) ∨ (p5 → p5))) → (p2 → (p4 ∧ p4)))) → (((p3 → p1) ∧ p3) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80260642733541646271480379911 : ((((p5 ∨ (p1 ∨ ((p3 ∨ ((p3 ∧ p4) ∨ ((p5 ∧ False) ∧ (p4 → True)))) ∧ (p2 ∧ (True → p3))))) ∨ (p1 → p1)) → (p1 ∧ False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ (p1 ∨ ((p3 ∨ ((p3 ∧ p4) ∨ ((p5 ∧ False) ∧ (p4 → True)))) ∧ (p2 ∧ (True → p3))))) ∨ (p1 → p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258836658824884125086154475417 : ((True → p1) → ((((p5 ∨ (p3 ∨ p5)) → True) ∧ (((False ∧ (True ∧ p5)) ∨ (True → p2)) ∨ ((p1 → (p5 ∨ p1)) ∧ p4))) ∨ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39225885114043586857920231784 : (((True ∧ (p3 ∧ ((True ∨ p3) → ((p3 → ((True ∨ (True ∧ (((p2 ∧ ((p4 ∨ True) ∨ p3)) → False) ∧ p3))) ∧ p1)) ∨ p1)))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50707588461634386139607625563 : ((((p4 ∨ p1) ∧ ((((p5 ∨ (((p3 ∨ p4) ∨ ((p2 ∨ p1) ∧ p5)) ∨ True)) ∨ p4) → p3) ∧ p2)) → (True ∧ ((p3 ∧ p3) ∧ p2))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((p5 ∨ (((p3 ∨ p4) ∨ ((p2 ∨ p1) ∧ p5)) ∨ True)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h3.left
    let h11 := h3.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : ((p5 ∨ (((p3 ∨ p4) ∨ ((p2 ∨ p1) ∧ p5)) ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h19 : ((p5 ∨ (((p3 ∨ p4) ∨ ((p2 ∨ p1) ∧ p5)) ∨ True)) ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h19
    -- One of the premise coincides with the conclusion.
    exact h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h15.left
    let h23 := h15.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h24 : ((p5 ∨ (((p3 ∨ p4) ∨ ((p2 ∨ p1) ∧ p5)) ∨ True)) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h25 := h22 h24
    -- One of the premise coincides with the conclusion.
    exact h25
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h27.left
    let h30 := h27.right
    -- One of the premise coincides with the conclusion.
    exact h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h27.left
    let h33 := h27.right
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73027157010874269134977231750 : (((((((((((p5 ∨ p2) → (p4 ∧ (True → p5))) ∧ (p2 ∨ p4)) → (p2 ∧ False)) → p2) ∧ p3) → True) → (p4 → p4)) → p3) ∨ False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((((((((p5 ∨ p2) → (p4 ∧ (True → p5))) ∧ (p2 ∨ p4)) → (p2 ∧ False)) → p2) ∧ p3) → True) → (p4 → p4)) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198636805788304055384008621447 : ((p3 ∨ (((p2 → False) ∧ (p3 ∧ p4)) → p1)) ∨ ((((p4 ∧ (((True ∧ p2) ∧ p1) ∧ True)) ∧ (p4 → True)) ∨ ((p4 → False) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262342755123840389416278188412 : (True ∧ (((p1 → (True → (p1 ∨ p2))) ∧ ((p1 ∨ ((True → ((p5 ∧ p2) ∨ ((p3 ∧ p4) ∨ p2))) → (p3 ∨ p4))) → (p5 ∨ False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151338209993935461267524605831 : (((p2 → ((((p3 ∨ p1) ∧ p1) ∨ (True → p5)) ∨ ((p1 ∨ (p3 ∧ p5)) → ((p2 ∨ p3) → p1)))) → True) → ((p5 ∨ (True ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745962667422663661788158378534 : ((((False ∨ p4) → ((p2 ∧ (p2 ∧ False)) ∨ (((p4 → (p4 ∧ p4)) ∧ (p4 → (p3 ∧ p4))) ∧ ((p5 ∨ (p2 ∧ True)) ∨ (p4 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173684621659055827404360561068 : ((((True → ((p1 → p2) ∧ ((False ∧ (p1 ∨ p1)) ∨ (p1 → False)))) ∨ False) ∨ True) → (((((p1 → True) → True) → (p5 ∨ p5)) ∧ p5) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113502025962514404045789049981 : ((((((False ∧ (p3 ∧ (False ∨ (((False ∧ p1) ∧ False) ∧ p4)))) ∧ True) ∧ p3) ∧ ((p1 ∨ (p2 → p5)) ∧ p3)) ∨ (p5 ∨ True)) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253798653313465265306624229629 : ((p1 ∧ p2) → ((((p4 ∧ ((p3 ∧ p1) ∧ (p1 → p4))) ∧ ((p3 → (p4 ∧ False)) ∨ (p3 ∧ False))) ∨ (p2 ∨ p1)) ∧ (p5 ∨ (p2 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62672442160874480595013053659 : ((p4 ∧ (((p4 ∧ True) → ((p5 ∨ ((p2 ∨ (((p2 ∨ (True ∨ False)) ∧ p2) ∧ p1)) ∧ p5)) ∨ ((p2 ∧ p3) ∨ (True → True)))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164976366861807672931761461033 : (((((p2 ∧ (p1 ∨ (p3 ∨ (((p1 → False) ∧ p3) ∧ p4)))) ∨ p2) → (p2 → True)) → p3) ∨ ((((p2 → p2) ∨ (p5 ∧ False)) → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190436899351636151086626597738 : (((True → ((p3 ∨ p3) ∨ (False ∧ (p5 ∨ p4)))) ∨ p5) ∨ ((((p1 ∧ (p3 → (p3 ∨ p2))) → (p5 ∨ p4)) → True) → (p4 ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315137268124071918795021195687 : (p3 ∨ ((p4 ∨ ((p5 → p3) ∧ (p4 ∨ p2))) ∨ ((p5 ∧ ((((p1 ∨ p5) → p4) → p4) ∧ False)) → ((p5 → True) ∨ (p4 ∧ (p1 ∨ p4)))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238265672018137750908240340704 : ((True ∨ p5) ∧ ((p2 ∨ ((p4 ∨ p3) ∨ p4)) ∨ (((p3 ∧ ((p5 ∧ p2) ∨ (False ∨ p1))) ∨ (p3 → (p1 → True))) ∨ ((p1 ∧ p4) ∨ p3)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98831176351323660391558102663 : ((True → ((p4 → ((True ∧ ((True ∨ (p5 → ((False ∧ (p4 ∧ p3)) → p4))) ∧ ((True ∨ (True ∧ (True → p3))) → False))) ∧ False)) ∧ False)) → p5) := by
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
theorem thm_5_vars_51528128737329609232948694579 : ((((p2 ∨ True) → (p2 ∨ ((p5 → p5) ∨ (((p4 ∨ (p3 ∨ (p2 → p3))) → p5) ∨ False)))) → (p5 ∧ ((p4 ∨ p4) ∧ (p1 → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135189839480265928664620845915 : (((((True → ((p5 ∨ False) ∧ ((p2 → (((True → p5) ∧ True) ∨ False)) → True))) → (p4 ∧ p5)) → True) → (False ∨ p5)) ∨ (True ∨ (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255752593684374401202501740881 : ((True ∨ True) → ((p1 ∨ ((p4 ∨ ((True → p2) → p3)) ∧ p3)) ∨ (((p2 ∧ True) ∨ (p4 ∧ p2)) ∨ (((p2 ∧ p2) → (False → False)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677881192461234673234275969800 : ((((((((p5 ∧ (p1 ∨ p1)) → p4) → ((p5 ∧ p5) → (p3 → False))) ∧ (p3 ∨ False)) ∨ (p4 ∨ True)) ∨ (p4 → (p2 → (p3 ∨ True)))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_149400857834236373174253595097 : ((True ∧ (((((True ∨ (p5 ∧ (p3 ∨ (True ∨ ((p1 → (p4 ∨ p4)) → p4))))) ∨ p3) → p5) ∨ p3) → p1)) ∨ (False → (p2 ∧ (p3 ∨ p1)))) := by
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
theorem thm_5_vars_178622336091701499161557705765 : ((((p4 ∨ ((p5 ∨ p4) ∧ p1)) ∨ True) → (False ∧ (p3 ∨ (p2 ∨ p5)))) ∨ (p4 → ((False ∧ (p2 ∨ p4)) → ((p2 ∨ p2) ∨ (p2 ∨ p4))))) := by
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
theorem thm_5_vars_138268391835243667800572404948 : ((p2 → (p2 → (p3 ∨ (p3 ∨ ((((p3 → (True ∨ True)) ∨ p1) ∧ False) ∨ (p1 ∧ (p2 ∧ (p5 ∨ (p3 → p3))))))))) ∨ ((p3 → p3) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136461388319816177951377155039 : (((p3 → ((p3 → p3) ∨ True)) → ((((p5 ∧ p4) ∨ (((p4 → ((p5 ∧ p1) ∨ True)) ∧ False) ∧ p2)) ∧ p5) ∨ True)) ∨ (False ∧ (p4 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191540631112615222805616625962 : ((p1 ∧ (((True ∨ p2) → ((p4 ∧ False) → True)) → p5)) ∨ (False → (p5 ∧ (((p3 → ((p3 ∧ (True ∧ p2)) → p1)) ∨ False) ∧ (p4 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197044141261704842278607805522 : ((((p3 ∨ p1) ∧ (p4 ∨ (p1 → p3))) ∨ False) ∨ ((p3 ∨ False) → (((p1 → False) ∨ ((True ∧ ((p4 ∧ p3) ∨ (False → p3))) ∧ True)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760750025814911990653334829766 : (((p2 ∧ (False ∨ (p5 ∨ ((True → (((p2 → (((p1 → (((p3 ∧ True) ∧ False) ∨ (True ∨ False))) → p1) ∨ p5)) ∧ p5) ∧ False)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769313965181407863700819825965 : (((p5 ∧ ((p2 → p1) → (p5 → ((True ∨ p5) → ((((p3 → p3) ∨ (p1 ∨ (p4 ∧ p5))) → p1) ∧ ((True ∧ False) ∨ (p3 ∨ p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_398144879623757277033239367199 : ((((p4 ∨ (p1 ∧ (p1 ∧ ((((p2 → (p1 ∧ p3)) ∨ p4) ∨ (p5 ∧ p4)) → (False ∧ (p3 ∧ (((True → p4) ∨ p2) ∧ p4))))))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40539533128514225175476632401 : ((((p3 ∨ (p3 → ((False ∧ ((((False → False) ∧ p5) ∧ (p5 ∨ (p1 → False))) ∨ (p3 → ((p3 ∧ p4) ∧ p5)))) ∧ True))) ∨ False) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187209010102404598524060093595 : (((p5 ∨ p1) → ((True ∨ p4) ∧ (((p1 ∨ p4) → True) → p5))) → ((p3 ∧ (p4 → (False ∧ (False → (True ∨ True))))) ∨ ((p4 ∨ True) ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693327673283850663399158148800 : ((((True → (p2 ∧ (((False ∨ p1) ∧ True) ∧ ((False ∨ False) → (p4 → p3))))) ∧ (p2 → ((p1 ∧ True) ∧ (p2 ∧ (p1 ∧ (False ∧ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158395633406496748195571743595 : (((p4 → False) ∧ ((((p3 ∨ (((p1 ∧ p1) → False) → (False → p4))) ∧ (p1 ∨ p3)) → p5) ∨ False)) ∨ ((True → False) → ((p3 ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263880294263365766298828000531 : (True ∧ (((((p2 ∨ ((p3 → p4) → (p2 ∨ p4))) ∧ False) ∨ (p4 ∧ p2)) ∧ p3) ∨ (p4 ∨ ((True ∧ (p2 ∨ p4)) → (False ∨ (True ∨ p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183394127021245764351103898619 : ((False ∨ ((p1 ∨ (p4 ∨ p2)) ∨ ((p5 → True) ∨ (p2 ∧ p5)))) ∧ ((((p5 ∧ p1) ∧ p4) → (p3 ∨ True)) ∨ ((p2 ∨ (p1 ∧ p5)) ∧ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136970919714609301010710501427 : (((p2 ∧ p1) → (((p2 ∨ p4) ∧ ((p5 ∨ (p1 → (p4 ∨ p5))) → (p4 ∨ p5))) → (p5 → (p2 ∧ (False ∧ p5))))) ∨ (p1 → (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241850959406065969122768958962 : ((p1 → p1) ∧ ((p5 ∧ (False ∨ p1)) ∨ ((((p3 ∨ p1) ∧ p1) ∧ (((((p2 → p1) → (p5 ∨ True)) ∧ (True ∨ p2)) ∨ p4) ∧ p1)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706564501855124517001796612857 : ((((False → ((p2 ∧ True) → (True ∨ (p5 ∧ p2)))) ∧ (((((p4 ∧ p1) ∧ p4) → p2) ∧ p3) ∨ ((p1 ∧ p2) ∧ (False ∧ (True → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180892264718127428932509664151 : ((((True ∨ True) → p1) → ((p3 ∧ (((p1 → p5) ∨ p1) ∧ False)) ∧ p3)) → (p1 ∨ (((p4 ∧ (p2 ∧ p1)) ∧ p2) → (p5 ∨ (p1 → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((True ∨ True) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h9
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64271367290457241376788897931 : ((False ∨ (True → (p1 ∨ (((p2 ∧ p4) ∨ p3) → (((p3 ∧ (True ∨ (p4 ∨ False))) ∧ p3) ∨ ((((p2 ∧ p2) → False) ∨ False) ∨ p4)))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157266693415940586695276457524 : (((((p4 ∧ p5) → True) ∧ ((p1 → ((((p2 ∨ p2) → (p4 → True)) ∨ p3) ∨ p1)) ∨ p5)) → p2) ∨ ((((False ∨ p3) ∧ p3) ∨ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178863657254388730631605499481 : (((False → (False ∨ p3)) → ((((p5 → p5) ∨ (p3 ∧ p5)) → p5) ∧ p1)) ∨ ((p5 ∨ (p4 → (p3 → p4))) ∨ ((p2 → True) ∧ (p4 ∧ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234238273138741294341667044914 : ((False → (p2 ∨ True)) → (p4 ∨ (p2 → (((((p5 ∨ False) ∧ p1) ∧ p4) ∧ (True → p2)) ∨ (True ∨ ((p3 ∧ (p5 → (p2 ∨ p3))) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215599681205640293066184464669 : ((p5 ∧ (p4 ∨ (p2 ∧ p5))) ∨ ((((((p4 ∧ (p3 ∧ (True ∨ p1))) ∨ p5) ∨ ((p5 → p2) → (p2 ∨ (p1 ∨ p3)))) ∧ True) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_81162058346579339335891921135 : (((p1 ∧ ((((p1 ∨ (p3 → False)) → p3) ∧ p5) ∧ (True ∨ (((p5 ∨ p1) → p5) ∨ (p5 ∧ (False ∨ False)))))) ∧ ((p5 ∧ p2) ∨ p1)) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h14 : (p1 ∨ (p3 → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h15 := h8 h14
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h17 : (p1 ∨ (p3 → False)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h17
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h24 : (p1 ∨ (p3 → False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h25 := h8 h24
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h27 : (p1 ∨ (p3 → False)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h28 := h8 h27
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176908211063689798502611469591 : (((True ∨ p5) ∨ (False → ((p2 ∧ ((p5 ∨ True) ∨ p4)) ∨ (p4 → p5)))) ∧ ((((p3 ∨ ((p4 ∧ (True → True)) ∨ False)) ∨ p2) ∨ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



