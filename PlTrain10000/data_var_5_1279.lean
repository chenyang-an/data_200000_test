variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157863590394351960232886210761 : (((True → (p4 ∨ (((p2 → (p5 → p5)) ∨ p2) ∧ False))) ∧ (((p3 ∧ (p5 ∨ p1)) ∧ p5) ∧ p4)) ∨ (False ∨ ((p4 ∨ (False ∨ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668301964413745477285125898270 : ((((p4 → ((p2 ∧ ((False ∨ (((True ∧ ((False ∧ p5) ∧ p3)) ∨ (p1 ∨ False)) ∧ True)) ∧ p4)) ∨ (p5 → False))) ∧ ((p1 ∨ p3) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178813357768876762621616661093 : (((p3 ∧ (False → True)) ∨ (True → ((p1 ∨ ((p3 ∧ p4) ∧ p1)) ∨ p5))) ∨ ((False ∨ (p2 → p2)) ∨ ((((p1 → p4) → p2) ∨ True) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55582973168451912158169229854 : (((p2 ∨ ((p3 ∧ (p3 ∨ p1)) → p2)) → ((((p3 → p5) → (((p3 → (False ∧ False)) ∨ p5) → (False → p2))) ∧ p3) → (p4 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57672911254604973321519193417 : ((((False → p5) ∨ p1) → (p3 ∧ ((True → (True ∨ p1)) ∧ (((((p2 ∧ (p4 ∧ ((True → p3) → False))) → p4) ∧ p1) ∧ p4) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206513279984977208334515334377 : ((p5 ∨ (p3 ∨ (False ∧ (p1 → False)))) ∨ (p3 ∨ (p2 → (((p5 → p3) ∨ False) → (p2 ∨ (p1 → (((p5 ∨ (p5 → p2)) ∧ p5) → p4))))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157827264535983661437774426944 : (((True ∧ (((False → (True ∧ (False ∨ (False → p2)))) ∨ True) ∨ p1)) → (p4 ∨ (False ∨ (False ∨ True)))) ∨ ((p1 ∧ (False ∨ p3)) ∧ (p3 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37367164999748473081680201097 : (((((p3 ∧ (((((p1 ∧ ((p1 → p4) ∧ p5)) ∨ p2) ∧ p3) ∨ p1) ∨ ((p3 → (p5 → p1)) ∧ (False ∨ p1)))) ∨ p1) ∨ True) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166574858021524257123199400828 : ((True → ((((p4 → (((True → p2) ∨ (p3 ∨ (True → p4))) ∨ p5)) → p4) ∨ p3) → p5)) ∨ ((((p4 → p4) ∨ (p1 ∨ True)) ∨ p2) ∨ p3)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213562527361998956653446064998 : ((((False ∨ p3) ∧ p5) ∨ p4) ∨ (((p3 ∨ (p1 ∧ (p2 ∧ ((p5 ∧ p2) → p5)))) ∧ ((p3 → ((p2 ∨ (p5 ∨ p5)) ∧ False)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148961423751752772081654475204 : ((((False ∨ p1) ∨ p2) ∧ ((True ∨ ((p3 → (p3 → (p2 ∨ p1))) → p2)) → (p3 ∧ (p1 ∨ (True ∧ True))))) ∨ ((p5 ∨ (p3 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152989888653356498401815069901 : ((p1 ∧ ((p4 → p4) → ((p2 → (((p3 ∨ False) ∨ (False → p2)) ∧ (True ∨ (p1 ∧ p1)))) ∧ (p2 → p1)))) → (((True → p1) → p2) ∨ p1)) := by
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
theorem thm_5_vars_199238918514162726522046127276 : (((False → (p4 → (p2 ∧ (False ∨ False)))) ∧ True) → ((((p2 → (p1 → (p1 → p2))) ∨ (False → (p4 ∧ (p5 ∧ p5)))) → p4) → (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : ((p2 → (p1 → (p1 → p2))) ∨ (False → (p4 ∧ (p5 ∧ p5)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h5
  -- One of the premise coincides with the conclusion.
  exact h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h12 : ((p2 → (p1 → (p1 → p2))) ∨ (False → (p4 ∧ (p5 ∧ p5)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h16 := h2 h12
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48352894457484586305943769085 : (((p3 ∨ (True → (p3 → ((True → p3) → (p3 ∨ (p1 ∨ (((True ∨ p3) → (p2 ∨ p2)) ∧ ((p1 ∨ p1) ∧ p4)))))))) → (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357416336006368809698941322349 : (p5 → ((p1 ∨ p3) → (((p2 → (p3 ∨ (((p5 ∧ (p4 ∨ ((p1 ∧ p4) ∧ p2))) ∨ p3) ∨ (p4 ∨ p2)))) ∨ False) ∨ (True ∧ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789356530556285274731353035873 : (((p5 ∨ (((True → (p4 ∧ p5)) → (p1 ∨ ((p4 ∨ p1) ∨ ((p5 ∧ p4) → (True ∨ p2))))) → (p4 ∨ (p2 ∧ (p4 → (False ∨ True)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166206815251574214723854154819 : ((p1 ∧ (p3 ∨ (False ∧ (((p1 → True) ∧ (p2 ∧ p3)) → ((p5 ∧ False) ∨ (True ∨ p1)))))) ∨ (p4 → (p4 ∧ (True ∨ (p1 ∧ (p1 ∧ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46882189571126122165630689028 : (((((True ∧ ((p4 ∧ True) ∨ (((p3 → ((False ∧ p2) ∧ p3)) ∧ (p2 → ((False → p4) ∨ p5))) → p4))) ∧ p1) ∨ False) ∨ (p4 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85820086654366037932121193361 : ((((p3 ∧ p1) ∨ ((True → (((True ∨ False) ∧ False) ∧ p2)) → p3)) → (((False ∨ True) ∧ ((p5 ∧ (p1 ∧ p4)) ∧ p4)) ∧ (False ∧ p2))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ p1) ∨ ((True → (((True ∨ False) ∧ False) ∧ p2)) → p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117818820916410628322697486127 : ((p4 ∧ (True ∧ (((p3 → (p5 → (((p2 ∧ p1) → (p5 → (p5 ∨ p1))) → (p5 → True)))) ∧ (p4 ∧ (p2 ∧ p1))) ∧ p2))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342165528399860502926232331646 : (p2 → ((((False ∨ p2) ∨ p3) ∧ (((False → (p2 ∧ (((False → p1) ∨ False) → p3))) ∨ False) → (p5 ∧ p5))) ∨ (True ∨ (p3 ∨ (p5 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591227346590079314272222333359 : (((((((((p4 ∧ p5) ∨ True) ∧ (p3 ∨ (((True → ((False → p2) ∧ p4)) → p1) → False))) → False) ∧ (True ∨ p2)) ∧ (True ∧ p4)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708349810319164076219262752359 : ((((((p1 ∨ (p5 ∧ (p4 ∧ False))) → p1) ∧ p5) → (p2 ∧ (p3 ∨ (p2 ∨ ((p1 → (p4 ∨ (p3 ∨ p4))) ∨ ((p4 → p2) ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658504082882156456013439840574 : ((((p2 ∨ (((p3 ∨ (p2 → p3)) → (p3 ∨ ((p1 ∨ ((p2 → ((p3 ∨ (p4 ∧ p3)) ∨ p4)) ∨ p3)) → p4))) ∧ p1)) ∨ (p1 → True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_58432928766061479981051018682 : (((p2 ∨ p5) ∧ (p2 → (False ∧ ((p3 ∧ ((((False → False) ∨ ((p4 ∧ True) ∧ (p1 ∨ p5))) ∧ p2) → p4)) ∧ (True ∧ (True ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343431109086419388525389036663 : (p2 → ((p1 ∨ p5) ∨ (p3 ∨ (((((((p5 → (p1 ∨ p1)) ∨ (p1 ∧ p4)) ∧ p2) ∨ (True ∧ p2)) ∨ p2) ∧ ((p3 ∨ p4) → p2)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227872493842827257658910114145 : ((p2 ∧ (p4 ∨ True)) ∨ (((p2 → p3) ∧ ((p4 → (((p5 ∨ p2) ∨ p1) → ((p5 ∧ p2) ∨ (True ∧ p3)))) → p2)) ∨ (p3 → (p2 ∨ True)))) := by
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
theorem thm_5_vars_114870051015142341626744172999 : ((((p4 ∨ (((p3 → True) ∨ p1) ∨ p5)) → (p2 ∨ ((True → p2) ∧ False))) ∨ (True ∨ ((p2 ∨ p5) ∨ (False ∨ (p5 → False))))) ∨ (p4 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141490617512601902289599483900 : (((p1 → (p3 ∨ p5)) ∧ (p3 → ((p4 ∧ (((p4 ∧ True) ∧ True) ∨ ((((p2 ∨ p3) ∧ p5) → p3) → True))) ∧ p1))) → (p4 → (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60090089336413548730528682641 : (((p3 ∨ True) → ((p1 → p1) ∧ ((p4 ∧ ((p1 ∧ True) → (((p1 → p4) → p2) ∨ ((p5 ∧ p1) ∧ (p3 ∨ (True → True)))))) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_56192416564392152702230623507 : (((p5 ∧ ((True ∨ False) ∨ p3)) ∨ ((((p5 ∨ (False ∧ ((p4 → (p1 ∨ p4)) ∨ p4))) ∨ p4) ∨ ((True ∧ False) → p1)) ∨ (p5 ∧ True))) ∨ p1) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704350284601773666190022769304 : (((((((p1 → p3) → p5) → True) → ((p5 ∧ p5) ∨ p1)) → (((p2 ∨ p5) → (((p3 ∧ False) ∧ ((p4 ∧ True) ∧ p1)) ∧ True)) ∨ True)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114941681201536531733634641804 : (((((p4 ∧ p4) ∧ p2) ∨ (True → (((p4 ∧ p3) ∨ (p4 → True)) ∧ p2))) → ((p2 ∨ ((p3 ∨ False) → p2)) ∧ (p1 → p2))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2288557927037091527916275100 : (((p4 ∧ True) ∨ ((((p1 ∨ p4) ∨ p5) ∧ (p3 ∨ False)) → (False ∨ p5))) ∨ ((p4 → ((False → (p2 ∨ True)) → (p4 ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85342784849229723914070229092 : ((((p2 → (p1 → ((p3 ∨ p3) ∨ ((False ∧ p4) → p5)))) → False) ∧ ((p3 ∧ False) ∨ (True → (p5 ∨ (p1 ∨ (p1 → (p1 → False))))))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p2 → (p1 → ((p3 ∨ p3) ∨ ((False ∧ p4) → p5)))) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h8
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106295311472508852258787119012 : ((((((((p1 ∧ p1) ∧ False) ∧ True) ∨ p4) ∧ True) ∧ p4) ∨ (True ∨ (False ∧ (p5 ∨ ((True ∨ False) ∨ (p1 → (p2 → p5))))))) ∧ (p2 → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148984350380232269621225124548 : (((p5 ∧ (p4 ∨ p1)) ∧ (((p2 ∨ (p3 → (p5 → ((p5 ∧ ((p5 → p3) ∧ p3)) ∨ True)))) ∨ p3) ∧ p4)) ∨ ((p3 ∨ (p2 ∧ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172799034202078547202731710243 : (((p4 → False) → ((True → (True → (False ∨ (True ∨ ((True ∨ False) → p3))))) → p2)) ∨ (p5 ∨ (((False → (False ∨ p5)) ∧ (False ∧ p1)) → p2))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43932236607431237003717740003 : ((((((p5 ∧ (((p2 → p4) ∨ False) → p1)) → ((p4 → ((p1 ∨ p4) ∧ True)) → p5)) → (False → (p5 ∧ True))) ∨ (p4 → p4)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245790085917860145491532993493 : ((p3 ∧ p3) ∨ (((p5 ∨ ((True → True) ∨ (p4 → (p2 → (False ∧ p1))))) → False) ∨ (p4 ∨ ((p4 → p1) → (((p4 ∧ True) ∧ p3) ∨ True))))) := by
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
theorem thm_5_vars_138050192880834844791639450140 : ((True → ((p1 → p5) ∧ ((p4 → ((p3 → False) → ((p4 ∨ (((True ∧ p1) ∨ p4) ∨ (p2 → True))) ∨ p3))) → False))) ∨ ((False ∧ p1) → False)) := by
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
theorem thm_5_vars_728256779441387430247315902747 : ((((True → (p4 → p3)) ∨ ((p5 ∧ False) ∨ (p4 ∧ ((p2 ∨ ((p5 ∨ p1) ∧ p3)) ∧ ((((p5 → True) ∧ p2) ∧ p3) → (p1 ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209531346414496502735090911697 : ((p4 → (True ∧ (p3 → (p3 ∧ p5)))) → ((False ∧ ((((p3 ∧ ((p2 ∧ p3) → p4)) → p2) ∨ p3) ∧ (False ∨ p4))) ∨ ((p5 ∨ p5) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157157581177463703772378630985 : (((((True → p2) → (p5 → ((p3 ∧ ((p4 → (p4 ∨ p5)) ∨ p3)) → (p3 → p4)))) ∨ p3) → p2) ∨ (False → ((p2 → p3) → (p2 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8179117928024714928213971175 : ((((p4 ∨ (((((p3 ∧ (((True ∧ p2) ∧ (True → p5)) ∧ (p3 ∨ p5))) → p4) ∧ ((p3 ∨ False) ∨ p1)) → p1) → p5)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_668817929324458287854036640244 : ((((((True → ((((p4 ∧ p1) ∧ (p2 → (p4 ∨ True))) ∨ p4) ∨ p4)) → ((True ∧ False) ∧ (p2 → p5))) ∨ p1) ∨ (p5 → (False → p2))) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135420496123279179655911506374 : (((False ∧ ((p1 → ((p3 ∨ (p4 → True)) ∧ (p3 → p3))) → (((p4 → p5) → p4) ∧ p4))) ∨ ((True ∨ p3) → p3)) ∨ (True ∨ (True ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348832984812293050468503232315 : (p3 → (p1 ∨ (p2 ∨ ((True ∧ (p1 ∧ ((True → False) ∧ ((p2 ∨ p5) ∧ (((True → p3) ∨ (False → False)) ∧ p5))))) → (True ∧ (p2 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h10.left
    let h18 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h20 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h21 := h7 h20
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h24 := h7 h23
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136159558289081085317076766157 : (((True ∨ (((p4 ∧ p5) ∧ p2) ∨ (p3 ∨ p4))) → (((p3 ∨ (p4 ∧ ((p3 → p1) ∨ (p4 ∨ False)))) ∨ p4) ∨ p1)) ∨ ((p5 ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257428922531471999464820111308 : ((p3 ∨ True) → (((((False ∨ False) → (False → (False ∨ (False → True)))) ∧ p4) ∧ ((p3 → False) ∧ ((True → (p2 → (p3 ∧ p4))) ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_60087604994725780494628832107 : (((p3 ∨ True) → ((((False → (p1 ∧ p5)) ∧ ((((p4 → True) → p3) ∨ (p5 ∨ (p1 ∨ (p1 ∧ p4)))) ∧ p4)) → (p2 → p3)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309654063894336821661820909820 : (p2 ∨ ((p1 ∨ (True → ((p5 ∨ (((p5 → p4) ∨ (((p1 → ((p1 ∧ p1) ∨ p1)) → p2) ∨ p2)) ∨ p5)) ∧ p4))) ∨ ((p3 ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_590304953739357919813000113213 : (((((((p2 → p1) → p5) ∧ ((((p5 ∧ p5) ∨ ((False ∧ (((True → True) → (p4 ∧ p3)) → p5)) → p1)) ∧ p2) ∧ True)) → p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629098245087754201965215986801 : ((((((((p1 ∨ (p4 ∨ p5)) ∧ ((((p2 → p3) → (p4 → (p5 ∧ ((p4 ∨ p2) → p4)))) ∧ True) → p3)) → True) ∨ p3) ∨ p3) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84700365697445161729541582074 : (((((True ∨ ((p2 ∨ (True ∨ p1)) → (p3 ∨ False))) ∨ (p5 ∨ p5)) → False) ∧ (p3 → ((((p3 ∧ p1) ∨ p5) ∨ p1) ∨ (p1 ∨ p2)))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ ((p2 ∨ (True ∨ p1)) → (p3 ∨ False))) ∨ (p5 ∨ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685760073088129621079443975715 : (((((((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) → False) → (((p2 ∨ p5) → (p1 ∧ p1)) ∧ p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : (((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : (((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (((True → ((p1 → (False ∨ (p1 ∨ (p5 ∧ p5)))) ∨ (p3 → p1))) ∨ p5) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h16
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h15
  -- False on the left can always be used.
  apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336143844922122948772741205619 : (p1 → (((p5 → ((((p2 ∧ True) ∨ (((True ∧ (True → True)) ∧ (p2 ∧ p4)) → p4)) ∧ (False ∧ (True ∨ p2))) ∧ (False ∨ p2))) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343008037486130323610013262834 : (p2 → ((p1 → (p3 ∨ (True → False))) ∨ (((p3 ∨ ((p1 ∧ ((p5 → p2) ∨ True)) ∨ p5)) ∧ p2) → ((p5 → False) ∨ (p1 → (p4 → p1)))))) := by
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
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145054560967187055148899900728 : ((((p1 ∧ (((p1 ∨ p3) ∧ p2) ∨ p3)) → (p4 ∨ (p2 ∨ p4))) → ((True ∧ (True → (True → p5))) ∨ True)) ∧ (p3 ∨ (False ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_340133516278890961433964961867 : (p1 → (p3 → (p2 ∨ (((((p3 ∨ (p2 → p5)) → False) ∨ (p4 ∧ (False → p2))) ∨ True) ∨ (p3 ∧ (((p5 ∧ True) ∨ (p3 ∧ p4)) → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657713754717757653090460509588 : (((((p4 → True) → (((False ∨ p1) ∨ ((p2 ∨ p5) ∨ (((False ∨ (p3 → (p1 ∧ p5))) ∨ True) → (False ∨ p4)))) → p2)) ∨ (True ∨ p3)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_204469402231103232827816914180 : ((((p3 → (p5 ∧ False)) ∧ False) ∨ p3) ∨ ((p5 ∧ p4) ∨ (p1 ∨ (((p1 ∧ False) ∨ (True → (p2 ∧ ((p3 → p1) ∧ (True → p3))))) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166443014482787249503922631577 : ((p2 ∨ (((p3 → (((p1 → p1) → p4) ∧ p5)) → ((p5 ∨ (p2 ∨ p5)) ∧ p2)) ∨ p5)) ∨ (True ∨ ((p4 → False) ∨ (p4 ∧ (p5 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358247374573937288283257727679 : (p5 → (p4 ∨ (((p2 ∨ p2) ∧ p1) → ((p3 ∧ (p3 ∨ p2)) ∨ (p1 ∨ (False → (True ∨ ((p3 ∧ (p5 → p3)) ∨ ((p3 ∨ p4) → p1))))))))) := by
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
  cases h3
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346318997419503607135715052459 : (p3 → (((p1 → ((p5 ∧ True) ∨ (((p3 ∧ p3) ∨ (p4 ∧ p5)) ∧ ((p1 → (False ∨ p3)) ∧ (p3 → p4))))) ∨ (p2 → True)) ∨ (p5 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112928153593462770739383162949 : ((((p4 ∧ p2) → (p1 ∨ (p4 ∨ ((p3 → (((p3 ∧ ((True ∧ p3) → p5)) → p3) ∨ (p4 ∨ (p3 → p5)))) → p3)))) → p5) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351750764057150861043135242514 : (p4 → ((((p2 → (((p3 ∧ p3) → ((p1 → True) ∧ p3)) → p5)) ∨ p1) ∨ p5) → ((p3 → (p2 ∨ p5)) → ((p1 → p3) ∨ (True ∨ p3))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46908120971086272563900892651 : ((((((p4 ∧ True) ∧ ((True → p1) → ((p3 ∨ ((p4 ∧ (p5 ∧ p1)) → p2)) ∧ True))) → ((p3 → p2) → p2)) ∨ p3) ∨ (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208049603137930991255583450315 : (((True ∨ (p3 ∨ p1)) ∨ (p5 → False)) → ((p2 ∧ (p4 ∧ ((((True ∨ (p3 ∧ p5)) ∨ (p3 ∨ ((True ∧ p4) ∨ p5))) ∨ p3) → p1))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135786068507891005985709873723 : (((((True → ((p5 ∨ (p1 → True)) → True)) ∧ True) → ((p1 → False) ∧ p5)) → ((p4 ∧ (p5 → (False ∨ p2))) ∨ p5)) ∨ (p4 ∨ (True ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → ((p5 ∨ (p1 → True)) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192341159046371961829213448242 : (((p3 ∨ ((p5 ∨ p5) ∨ (p1 ∨ (p3 ∧ False)))) ∧ p1) → ((((p2 ∧ p4) ∨ (True ∨ ((p5 → False) ∧ p3))) → p1) → ((p4 ∨ p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41290568131349290199478607519 : (((((False ∧ ((p3 ∨ False) ∧ False)) → (False ∧ (((((True ∨ p2) ∧ p3) → p3) ∨ p4) ∨ p2))) → (p4 → (p3 ∧ (True ∨ p5)))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354857363285316419385459188048 : (p5 → (((True ∨ True) → (((((p2 ∧ (((True ∧ (p5 ∨ p3)) ∧ (p5 → p5)) ∨ p2)) ∧ (p2 ∧ True)) ∧ (False ∨ True)) ∧ p3) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42556368153064746120724759038 : (((p1 ∨ (p4 ∧ ((p4 ∧ (False ∧ False)) ∧ (((True → p1) ∧ p1) ∨ ((p1 ∧ p5) ∧ (p4 ∨ ((p4 ∨ (True ∧ p1)) ∨ True))))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94663188008319415459668049819 : ((p3 ∧ (((p5 ∧ (((p1 → (p4 ∧ False)) ∧ (p3 ∧ (p1 ∨ True))) ∨ ((p3 ∧ (p5 ∧ True)) → False))) ∧ (True → p1)) ∧ (True ∧ p1))) → False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h5.left
      let h17 := h5.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h5.left
      let h23 := h5.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h23
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h25 := h11 h24
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h5.left
    let h29 := h5.right
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h30 : (p3 ∧ (p5 ∧ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h31 := h27 h30
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802944288475934805336717072275 : (((p3 → ((((((p4 ∨ ((p4 ∧ p2) → (p5 ∨ False))) → (p1 → (p2 ∨ p4))) ∧ (True ∨ (True ∧ (True → p3)))) → False) → p4) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166323825759519825819326606649 : ((p5 ∧ (((p2 → p5) → (p1 ∧ (p1 → (p5 ∨ p2)))) → ((True ∧ (p4 ∧ p5)) ∧ p3))) ∨ ((False → (True ∨ p2)) ∨ (p4 ∨ (True → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178565832614310378544621100786 : ((((p3 ∨ p5) ∧ ((True ∧ p1) ∧ p4)) ∧ ((p5 → True) ∧ (False ∧ True))) ∨ (((p2 → (p5 → (p5 ∨ (p1 ∧ p3)))) → p3) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_395152139605286348200515676944 : ((((False ∧ (p5 ∨ (((((p3 → (p3 ∨ p3)) ∨ p3) ∨ ((p4 → p5) ∧ ((p3 ∨ (False ∧ p2)) ∨ p2))) → (p5 ∧ False)) ∨ p3))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_587261636210515620426976667869 : (((((((False ∨ (((p4 ∧ p2) ∧ (((p5 → p4) ∨ (True ∨ p3)) ∨ (False ∧ p3))) → ((p2 ∨ p5) → p4))) → p5) ∧ p3) ∨ p2) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167907557190473242007677807581 : ((((p1 ∧ True) → (p5 → ((True ∨ p2) ∧ p1))) ∧ (((p3 → (p5 ∨ p1)) ∧ True) ∧ p4)) → ((((p5 ∨ p4) → p2) → (p5 ∧ p5)) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309354157185960087788305422060 : (p2 ∨ ((((True ∧ ((p1 ∧ p1) ∧ (p2 ∨ (p3 ∧ p2)))) ∧ p2) ∨ (True ∨ (p5 ∧ ((p5 ∧ p4) → (p4 ∨ (False ∧ p2)))))) ∨ (p1 ∧ True))) := by
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
theorem thm_5_vars_49093615061068891579978769163 : (((((p5 → (((((p2 ∧ (True ∧ p2)) → p3) ∨ p2) ∨ p3) → p2)) ∧ (True → p3)) ∨ ((p3 ∧ p1) ∨ p3)) ∨ (False → (True → p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308843802334856577741896537521 : (p2 ∨ (((((p5 ∨ False) ∨ (p2 ∨ (p3 → (True → (((p4 ∧ (p4 → p3)) ∧ p2) ∨ ((p5 ∨ p3) ∨ p1)))))) ∨ (p4 ∨ p3)) → False) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ False) ∨ (p2 ∨ (p3 → (True → (((p4 ∧ (p4 → p3)) ∧ p2) ∨ ((p5 ∨ p3) ∨ p1)))))) ∨ (p4 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314867570161114000160668639759 : (p3 ∨ ((((p1 ∨ p4) ∨ p4) ∨ ((p5 → (True ∨ (False ∨ p3))) ∨ p3)) → ((p1 ∨ (((False ∨ (p1 → p3)) ∨ True) → (p3 ∨ False))) ∨ True))) := by
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
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
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
theorem thm_5_vars_115896003609241041219811623667 : (((((True → p3) ∧ p4) → False) ∨ (p1 ∧ (False ∨ ((p2 → (True ∧ (p1 ∧ ((False ∧ True) → (p3 ∧ p4))))) → (p5 ∨ p5))))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198669070839661044410616581317 : ((p4 ∨ ((((False → p5) ∨ p2) → p4) ∨ p5)) ∨ (True ∨ ((p5 ∧ p1) → ((((p2 → p5) → False) ∧ (p2 ∧ ((p5 ∨ p2) ∧ True))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58626611190001367216847474548 : (((False → p5) ∧ ((p1 ∧ (((p3 ∨ ((p1 ∧ (p2 ∧ (p4 → p5))) → p1)) ∧ ((p5 ∧ p2) → p1)) ∨ p2)) → (p5 → (False ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116197597952828227841512536642 : ((((p1 ∨ p5) ∧ False) ∨ (((p1 ∧ (p2 → (False ∧ ((p1 → p5) → p4)))) → (((p5 ∧ p4) ∨ True) ∨ False)) ∨ (p3 ∨ p3))) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181288888642451461933982773936 : ((p5 ∧ ((((p4 → False) ∧ True) ∨ ((p1 ∧ (False ∨ p1)) → p5)) → p3)) → ((((p1 ∧ (p4 → ((p4 → p1) ∧ p2))) ∨ p1) → p3) ∨ p5)) := by
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
theorem thm_5_vars_49576070913406994208908231443 : (((((True ∨ (((p5 ∨ True) → True) ∨ (p3 ∧ p1))) ∧ (False → (p3 ∧ True))) ∨ (p1 ∨ (True ∨ (True ∧ p3)))) → ((False ∨ p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356458120768868990350293382343 : (p5 → ((p4 → ((p2 ∨ True) ∧ (p3 ∧ (((p3 ∧ True) ∧ p1) → p4)))) ∨ ((p3 ∨ (((((p1 → p2) ∧ p4) ∨ p3) → p2) ∧ True)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165445995934041466696996678376 : ((((p1 → ((p5 → (False ∨ p2)) ∨ (True ∧ p3))) ∧ p5) ∧ (False ∨ ((p5 ∨ p5) → True))) ∨ ((False ∧ ((False → p1) ∧ (p1 → p3))) → p4)) := by
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
theorem thm_5_vars_760846691676783148961093885616 : (((p2 ∧ (p3 ∨ ((p2 ∧ (((p3 → False) ∨ (p4 ∧ (p2 → (p2 ∨ (p1 → (p5 ∨ p4)))))) ∧ ((p5 → p4) ∨ True))) → (True ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48506289979023013740303415932 : (((((((p2 ∨ p5) ∨ ((((p2 ∨ p2) ∨ (p4 ∧ p4)) → p5) ∧ (True ∧ p1))) ∨ (p1 ∨ p5)) → p1) ∨ p2) ∧ ((p4 ∧ p4) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137750548539694384687150531526 : ((p2 ∨ ((((p4 ∧ (((((False → (True ∨ False)) ∧ True) → (p5 → True)) ∧ p1) ∧ p4)) → p3) → (p1 ∨ False)) ∨ True)) ∨ (True ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388234617176499638021764906493 : ((((((p3 ∨ ((p4 ∨ False) ∨ (False ∨ (p1 → p3)))) → (p1 ∨ (((p3 ∨ p5) ∨ p2) ∧ p3))) ∨ ((p3 ∧ (p5 ∧ p5)) → p5)) ∨ p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219032965482230835711001893226 : ((p5 ∧ ((p4 ∧ p1) ∨ p1)) → ((False ∧ ((p3 → p1) → (((True → True) → p3) ∧ (p4 → (p4 ∨ ((p5 ∧ (p4 ∧ False)) ∨ p2)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
theorem thm_5_vars_229755436086455979878820527529 : ((p4 → (p2 ∨ p5)) ∨ (((p3 → p2) → ((((((False ∨ False) ∨ True) ∨ (p5 → p5)) ∨ True) ∧ (p5 ∨ p3)) ∨ p2)) ∨ ((False ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40044436023309371501412930739 : (((((p4 ∨ (((p1 ∨ (False ∨ (p3 ∧ (p1 ∧ (True ∧ True))))) → p1) ∧ (p2 → (p1 ∧ (p4 → (p4 → p1)))))) ∧ p5) ∧ p2) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



