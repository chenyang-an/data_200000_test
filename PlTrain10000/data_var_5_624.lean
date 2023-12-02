variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117626937609296581708432047928 : ((p3 ∧ (((((p1 → (p1 ∨ p4)) → ((p5 → (True → (p5 ∧ p1))) ∧ (p4 → ((True → p5) ∧ p1)))) → p4) ∧ p1) ∨ p3)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121404622744895488675723730861 : (((((p5 → p4) ∧ ((p2 → ((p2 ∧ ((p3 ∨ p2) → (p2 ∨ (p1 ∧ (p3 ∨ p1))))) ∧ (p5 ∨ False))) ∧ False)) ∨ True) → False) → (False ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p4) ∧ ((p2 → ((p2 ∧ ((p3 ∨ p2) → (p2 ∨ (p1 ∧ (p3 ∨ p1))))) ∧ (p5 ∨ False))) ∧ False)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118342929435964537309765465579 : ((p2 ∨ (((p1 ∨ True) → (((False ∧ p1) → p1) ∧ (p3 ∨ (p4 ∧ (((True → (p3 ∨ p4)) ∧ (p4 ∧ p5)) → p3))))) ∨ False)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670928158046448708805383170130 : ((((p4 ∧ (((p4 ∨ p3) ∧ (((((False ∨ p2) ∨ p5) ∨ p2) ∧ (p1 → True)) ∧ ((True ∧ p1) → p1))) → p1)) ∨ (p3 ∨ (True → True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_185625706143637886767261181085 : ((True → ((True → True) → (p4 ∧ (p3 → (False → (p1 → p3)))))) ∨ ((((p3 ∨ p5) → p1) ∧ ((False → True) ∧ p5)) → (p2 → (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p5) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40694730424886764738535695270 : ((((((False → p4) ∧ (((((False → p5) ∨ p5) ∨ True) → (False ∨ False)) ∧ p5)) ∧ ((p4 ∧ False) → ((p5 → p4) ∨ False))) → p4) ∨ False) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h8 : (((False → p5) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h8
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184907943041607874456330446495 : ((((p4 ∨ p5) ∨ False) ∨ (((False ∧ p4) ∧ p2) ∧ (True → p3))) ∨ ((p3 → p4) → (p2 ∨ ((p1 → ((p3 ∧ p3) → p1)) ∨ (p3 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165882601300607115047393250611 : ((((False ∨ p5) ∨ p1) → (p5 ∨ (((p2 ∧ (p4 → True)) ∨ (True ∧ (p2 ∧ p2))) ∧ p5))) ∨ ((((False ∧ True) → p2) ∧ (False → True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115739919352633596640457112716 : ((((p1 ∨ p1) ∧ ((True ∧ p5) ∧ p3)) → (False ∧ (False ∧ (p3 ∧ (((((p3 ∧ p3) → p3) ∧ p4) ∨ p2) → (True ∧ p1)))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115044246144167395015260065997 : (((((p5 ∨ False) → ((p4 ∨ (p3 → (True ∧ p2))) → p4)) ∨ p1) ∨ (True ∧ (True ∧ ((p5 → (False ∧ False)) → (p1 ∧ True))))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172809450039556519812132586242 : ((True ∧ (((p4 → False) ∨ (False ∨ ((p4 → p5) → (False ∨ (True ∧ p2))))) ∨ True)) ∨ ((p3 ∧ ((p1 ∨ True) → (p5 → (False → p5)))) → p4)) := by
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
theorem thm_5_vars_588426183252626459896013680150 : (((((((p1 ∧ p5) ∨ p3) → (((((p1 ∧ p4) → p3) ∨ (True → (p5 ∨ (p2 ∧ p1)))) → (True ∧ p3)) ∧ (p5 → p3))) ∨ p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226599891093899992723590085473 : (((p5 → p1) ∨ p4) ∨ ((False ∨ (((p3 → p4) ∨ (((p2 ∨ (p3 → ((True ∧ (p2 ∨ p3)) ∨ p5))) → p3) → p3)) → (True ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_451624193861473823214352993952 : (((((p2 → (((False ∧ (p2 ∨ p3)) ∨ p4) ∧ (p4 ∨ (False ∧ p5)))) ∨ ((True ∧ True) ∨ (p5 ∨ True))) ∨ ((True ∨ (False ∧ p3)) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630723055839365517092607702222 : (((((p2 → (p5 ∨ ((((p2 → (p4 ∧ (p5 → p1))) ∧ ((True → p2) ∨ False)) → (p5 ∨ (p3 ∧ (p5 ∧ p4)))) ∧ p1))) ∨ p1) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113576568372363261268804474809 : (((False ∧ ((((((True → p3) ∧ ((((p5 ∧ p2) ∧ p3) ∨ True) ∨ (False ∨ p4))) ∧ p5) ∧ p5) ∨ True) ∨ True)) ∨ (p3 ∨ p2)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164533686172442711043485576290 : (((((p3 ∨ (p5 → p3)) ∧ ((False ∨ p2) ∧ (p5 ∨ p4))) ∨ (p3 → (False ∨ p2))) ∧ True) ∨ (((p1 ∨ (p3 ∨ (p5 ∨ p3))) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323513025204120009717781407799 : (p5 ∨ (((p3 ∧ p5) → ((p4 ∧ (True ∧ ((p2 → p1) ∧ (((True → (p4 ∨ p1)) ∨ (True ∧ True)) → p4)))) → p2)) ∨ ((p4 ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3390392005339763146160507694 : ((p2 → p3) → ((False ∨ ((p1 → (True ∧ ((p1 → True) → p5))) ∧ p4)) ∨ (True ∨ ((((True → p3) ∨ (p3 ∨ p3)) → p2) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115123574493723658587621973365 : ((((((p5 ∧ (p3 ∨ True)) ∧ p5) ∨ p3) ∨ (p2 ∧ (p2 ∨ p4))) → ((p2 → (p1 ∨ ((p3 ∧ False) ∧ p4))) ∧ (False ∧ True))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352865716918550633015425685071 : (p4 → (True ∧ ((((((p4 ∧ p1) → ((False ∨ p1) ∧ p4)) ∨ p3) → p1) → ((p2 ∧ p5) ∨ ((p3 → (p3 ∧ (p5 ∨ True))) ∧ p1))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p4 ∧ p1) → ((False ∨ p1) ∧ p4)) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h4.left
    let h8 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800209653333202276009296198790 : (((p2 → (((p4 ∨ (False ∨ (((p3 ∨ p3) ∧ (True ∨ (p4 ∧ ((False ∨ p3) → p2)))) ∨ ((p3 ∧ (True → False)) → True)))) ∧ p5) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232379498789779645758600101687 : (((p5 → False) → p2) → (p4 → ((((((((p4 → p1) → p2) ∨ (True ∧ (p1 ∧ False))) ∨ (p5 → p5)) → False) ∧ p2) ∨ p4) ∨ (p2 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217361403259968221238962760363 : (((p3 ∨ (p4 ∨ p1)) ∨ p1) → ((p5 → (p1 ∧ (((True ∨ (True ∨ False)) ∨ p3) ∧ p5))) → (False ∨ ((p5 ∧ False) ∨ ((True ∨ False) ∧ True))))) := by
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_149158227638199321673254825060 : (((p2 ∨ p3) ∧ (((((p3 ∨ False) ∨ (p4 ∨ (p3 ∨ True))) ∨ (((p4 → p2) → p1) ∨ p4)) → p4) ∨ p5)) ∨ (False → (p4 ∧ (p2 ∧ p1)))) := by
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
theorem thm_5_vars_698441249046274497900702190436 : (((((p5 ∨ ((False ∧ (p4 ∧ p1)) ∧ p3)) ∧ (p5 ∧ (True → p5))) ∨ ((p1 ∧ ((p3 → p4) ∨ (p4 ∧ p2))) → ((p2 ∨ p4) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337463684383543550584308559970 : (p1 → ((False → (p2 ∧ (((((False ∧ (p3 ∧ (((p1 → True) ∨ p3) → False))) ∧ p3) → p1) ∨ False) ∨ (p1 ∧ True)))) → ((p2 → p5) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729701798261416537822289515813 : (((((p2 → True) ∨ True) → (((((p4 ∧ (p1 ∧ (((((False → False) → True) ∧ p3) ∧ p3) ∧ (p1 ∧ p3)))) ∨ False) ∧ p1) ∨ p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115148577349557309462829394198 : (((p1 ∨ ((False ∨ (p4 → (p3 ∨ (False ∨ (p4 ∨ p2))))) ∨ True)) → (p4 ∧ ((p3 ∨ (p3 → p4)) ∨ ((p5 ∧ False) ∨ False)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316639651755506254786160808933 : (p3 ∨ (p4 ∨ ((p2 ∨ (p1 ∨ p1)) ∨ ((False ∧ (True ∨ (False → (True ∧ ((p3 ∨ (p4 ∨ (p2 → p3))) ∨ p4))))) → ((p4 ∨ p1) ∧ p2))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769336386382653266878960574777 : (((p5 ∧ (True ∧ (((((False ∨ p2) ∧ p3) → (p2 ∧ p5)) ∧ ((False → p4) ∨ (True → ((p4 ∧ (p2 ∨ p3)) ∨ (False ∧ p1))))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341661649778728528261574500984 : (p2 → (((((True → (p4 ∧ ((True ∧ ((True → p2) → (p5 → p3))) ∧ p5))) → False) → (False ∧ (p5 ∨ (p1 ∧ p2)))) ∧ p2) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798322580345335387818194278056 : (((p1 → (((((p3 ∨ ((p5 → False) ∧ False)) ∨ (p1 ∨ p2)) ∨ False) ∧ (p3 ∨ p5)) ∨ (True ∨ ((False ∧ (p3 ∧ p5)) → (p4 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323606912322391009434143251826 : (p5 ∨ (((False ∧ ((p3 ∨ (p1 ∨ (True → p5))) ∨ (False ∧ (p4 ∧ (p1 ∨ (False → (p1 ∨ False))))))) ∨ True) ∧ ((p2 ∧ p1) → (False → False)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318542307505829784288761093055 : (p4 ∨ (((((p5 ∨ p4) ∨ (((False ∨ True) ∧ (((p5 ∨ (p3 ∨ (p5 ∧ p1))) ∧ p4) ∧ (p3 → p5))) ∧ p3)) ∧ False) ∧ True) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790804948373015602890974042779 : (((p5 ∨ (p1 → (((p3 ∨ p4) ∨ (((True → (p3 → (True → p4))) ∨ (False ∨ p5)) ∧ p1)) ∨ (((False → p5) ∨ p4) ∨ (p1 → False))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63262207696729536494824856164 : ((p5 ∧ ((((p1 ∨ (p2 ∧ p2)) ∧ p4) ∨ p5) ∧ ((p3 ∧ False) ∧ (((p5 ∨ False) → p1) → ((p4 ∧ ((p1 ∧ p3) → p1)) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259127329463297766516200141749 : ((False → True) → (((((p2 ∨ (((p5 ∧ (False ∧ p3)) → (p2 ∧ ((False ∨ True) → p3))) ∨ p2)) ∧ False) ∨ (False ∧ (p3 ∧ p3))) ∨ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214785159155055083573589660190 : (((False ∨ p4) ∨ (p2 → p5)) ∨ ((p2 ∧ (p4 ∧ p1)) ∨ (True ∨ (p3 ∨ (p5 → ((((False ∨ p1) → p3) ∨ False) ∧ ((p2 → p2) → False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756631756856828525697869369574 : (((p1 ∧ ((p2 → ((p5 → (p5 ∨ p1)) → (p1 → (True → ((p3 ∧ (p1 ∨ p2)) ∨ p2))))) → ((True ∧ True) → ((True → True) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187851723092583531066314709396 : ((p5 → ((True ∧ False) ∨ (((True → p1) ∨ (p4 → p5)) ∨ p4))) → ((((p5 ∨ p1) ∨ (p5 ∧ p1)) → ((p2 → p4) → (p4 ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166044483596485352944099397190 : (((p5 → False) ∨ (p1 ∨ ((p5 ∧ p3) ∧ (((False → True) ∨ p4) → ((p4 ∨ True) ∨ p2))))) ∨ ((((p1 → p2) → (p1 → True)) ∨ False) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207763327718778642580992419661 : (((p2 ∨ ((p3 → p5) ∨ p1)) → p1) → (p2 ∨ ((p4 → p2) ∨ ((True ∨ False) ∨ (((((p1 → p1) ∨ True) → p4) ∨ (p3 → p2)) ∧ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114944592288546250488090379616 : ((((p2 ∧ p3) ∧ (((((True → p5) → p4) ∧ False) → True) ∧ (p3 ∨ True))) → ((p1 ∧ (((p2 ∨ p2) → p1) ∧ False)) ∨ p3)) ∨ (p5 ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39168268223970419083509787541 : ((((p5 ∨ p3) → (True → (False ∨ (p1 → ((((False ∨ (p2 → ((p2 ∨ p4) ∨ p2))) ∧ (p4 ∨ p1)) → (p4 → p5)) ∧ True))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262345831362713022837841932661 : (True ∧ (((True ∧ (p4 ∧ (p3 → p2))) ∨ (p2 ∧ ((p4 ∨ ((p2 → p4) → (((p2 → (p5 → (p5 ∨ False))) ∨ False) ∨ p1))) → False))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148254429265814732749459210907 : ((((p3 → p3) → ((True → p1) → ((True → (False ∧ (p2 → p2))) → (True ∧ p5)))) ∨ (p2 ∧ (True ∨ p4))) ∨ ((True ∨ p1) ∨ (p5 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654864257639339914210593874570 : ((((((((True ∧ ((p5 → (p4 ∧ (p3 → p1))) ∧ (False → p5))) ∨ p1) ∨ p3) ∧ (((p3 ∨ True) → p3) ∧ True)) → p2) ∨ (False → p3)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683650804561681967727575351087 : ((((((p4 ∧ ((p3 ∨ p4) ∨ p1)) ∨ ((p1 ∨ (p4 → p3)) → ((p5 ∧ False) ∨ p4))) ∧ p2) ∨ ((False → True) → (p2 → (True ∨ p3)))) ∨ p4) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135609215686954311074554823597 : (((p1 ∧ (((p2 ∨ p5) → ((p2 → (((True ∧ p1) ∧ p1) ∧ False)) → False)) ∧ False)) ∨ (p2 → (p5 → (False → p5)))) ∨ (p3 → (True ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161967318844573827946891999251 : ((p2 → (False ∨ (((False ∨ p5) → p1) → (True ∧ (p3 ∨ (((p5 ∧ (p1 ∨ p4)) ∨ p3) ∧ False)))))) → ((p5 ∧ (p3 → p4)) ∨ (p5 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53834214432100331585234883669 : (((((p1 → (p4 ∧ p4)) ∨ p2) ∧ (False ∨ (p5 → p1))) ∨ ((((False → (p5 ∨ p2)) ∧ (p5 ∨ p5)) → False) ∧ ((p5 → True) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215117431932165113743204320823 : (((p2 → p5) → (p3 → p4)) ∨ ((((False ∨ ((((p4 ∧ p2) → p3) ∨ (((p5 ∧ p3) → False) ∧ p3)) ∨ (False ∨ p1))) → p2) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59306296695834588701039140969 : (((p4 ∨ False) ∨ ((p1 → ((True → (p1 ∧ (((False → p3) ∧ ((p4 ∨ (p2 ∧ False)) ∨ p5)) ∧ (p3 ∨ (p4 ∨ p3))))) ∧ p5)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135397192507213056996393799919 : (((((True → p1) ∧ (((p1 ∨ False) ∧ p1) → ((p1 → True) → p1))) → (p3 ∧ (False ∧ p2))) ∨ (p1 ∨ (p5 ∧ p4))) ∨ (p5 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23650985238707954025271472001 : (((((p3 ∨ p3) ∨ p1) ∨ p5) ∨ ((True → (((p2 ∧ p2) ∧ p2) ∨ (False → ((p3 ∧ p5) → p4)))) ∨ (((p2 ∨ p4) → p5) ∧ p4))) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318634757294210749948226327513 : (p4 ∨ ((p4 ∧ ((p1 ∧ (((p1 ∧ p5) → ((p1 ∨ True) → ((p4 ∨ (p2 → (p1 ∧ False))) → True))) ∧ (True → p1))) ∨ p1)) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336181526302204884235142794476 : (p1 → (((p2 → ((p3 → ((((p5 ∨ p2) ∧ p2) → p5) ∧ ((((p2 ∧ p4) ∨ (p5 ∧ False)) → (p2 ∨ p1)) ∨ True))) ∧ True)) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47137367287594215081924712637 : ((((((p2 ∧ p5) ∨ ((p1 → (True ∨ p2)) → (p1 ∨ (True ∧ p4)))) → (p2 → p2)) ∧ ((False ∧ p2) ∧ (True → p4))) ∨ (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603780344656785913455136152925 : ((((p4 ∨ ((p5 ∧ ((((False ∨ p1) ∧ p3) ∨ p3) ∧ p4)) ∨ (True → ((p5 ∧ p5) → (True → (((False ∧ p2) ∨ p4) ∧ p4)))))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214710128177621186182914364845 : (((p1 ∧ True) ∨ (p3 ∧ False)) ∨ (((((p5 ∨ ((False → (p3 ∨ p4)) ∧ (False ∧ (p3 → p1)))) ∧ p1) ∨ False) ∨ p3) ∨ ((p4 ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46028482728693782336362468419 : (((((p5 → p2) → ((p5 ∧ (p3 → (True → p2))) ∧ ((False ∧ True) ∧ ((((p1 ∧ p2) ∧ p5) → p2) → p4)))) ∧ True) ∧ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174519093003537299581525805988 : (((p3 → (p4 → ((False ∨ p2) → p2))) ∨ (True → (((False → p1) ∧ p2) ∨ p3))) → (((p2 ∨ (p1 ∨ p4)) → p2) ∨ (p3 → (p5 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27815613780435684432647421031 : (((p5 ∨ p1) → (((((p2 ∨ p3) ∨ p4) ∨ ((False ∧ ((p1 ∨ p5) ∧ (p2 ∨ (p2 ∨ ((False → p5) ∧ p5))))) ∧ False)) ∨ p1) ∨ p5)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314742429287896793239702444041 : (p3 ∨ (((False ∧ (((p3 ∨ p5) ∨ (p5 ∧ (True → p2))) ∧ p1)) ∧ (False → p1)) ∨ ((p1 ∧ p5) ∨ ((False → (p3 ∨ p1)) ∨ (p1 ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51535402626721344857902257951 : (((True ∧ (p2 → ((((p3 ∨ p2) ∨ True) ∧ (True → False)) ∧ (((False ∨ p3) ∧ p4) ∧ p5)))) → ((((p5 → p4) ∨ False) ∨ True) ∨ p2)) ∨ p5) := by
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
theorem thm_5_vars_55230098265969581535636497733 : (((((p3 ∧ p5) → p2) → (p2 ∨ p3)) ∨ (p4 ∨ (((True → p2) ∨ (p2 ∨ (True ∧ p4))) ∨ (((False ∧ True) ∨ (p2 ∨ True)) ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217339999070721976104959528744 : (((p1 ∨ (p5 ∨ p2)) ∨ p5) → ((((((((True → p5) ∨ p2) ∨ p3) ∧ p5) ∧ True) ∧ (p2 → (((True → p3) ∧ p2) ∨ p5))) ∨ True) ∨ False)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51012360108085834432327371683 : (((False ∧ (((((p4 ∧ (p5 → (True → False))) ∧ p4) → (True → (p3 ∧ True))) ∨ p1) ∧ p3)) ∧ (False ∨ (p4 → ((p4 ∨ False) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52981741007860061921123665569 : ((((p3 → (p2 ∨ (((p1 ∧ True) ∧ p5) ∧ (True → p4)))) → p3) ∧ (((p3 → (((p2 → p1) ∨ p5) → (p5 ∨ p3))) ∨ True) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_128435614617506730092201946306 : ((p5 → (((True ∧ (((p4 ∨ p5) ∧ (False ∨ (p1 ∨ ((p1 ∧ (p2 ∧ (p4 → True))) → True)))) ∨ p4)) ∧ (p4 → p4)) ∧ False)) → (p5 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177701735122022553210106336835 : (((((((p5 ∧ (p2 ∨ p4)) → True) ∧ True) ∨ p4) → (p2 ∧ p5)) ∧ True) ∨ ((p2 → p1) → (False → ((p4 → ((p1 ∨ False) ∧ p4)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155440953741336278023316722888 : (((p5 ∨ (p1 ∧ (True ∧ True))) → (((p2 ∨ p5) ∨ False) ∨ ((p4 ∨ (p2 ∨ p1)) ∨ (p1 → False)))) ∧ (p1 ∨ (True ∨ (p3 ∧ (p5 ∨ p4))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49020569656613381322392165363 : (((((((((((True ∧ p1) ∨ p1) ∨ p5) ∨ (p5 → p2)) → True) ∧ True) ∧ p1) → ((False → p5) ∧ p5)) → False) ∨ (True ∨ (True ∨ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321304308206361006465519237345 : (p4 ∨ (p5 ∨ ((((((p3 ∨ False) ∨ (p2 ∧ p4)) ∧ ((True ∨ False) ∧ (p3 ∨ (p2 → p4)))) ∨ (p2 → p1)) ∧ (True ∨ p3)) ∨ (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110476438532500468607034230915 : ((p4 → ((((True ∧ (True ∨ (p4 ∧ p5))) ∧ (p4 → p1)) → ((False ∧ ((True → (p4 ∨ p3)) ∧ (p2 ∧ p5))) ∨ p1)) ∨ p3)) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h13 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h14 := h4 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350011580715620744505911405981 : (p4 → (((p2 → ((p1 ∧ (True ∨ False)) ∨ (((p5 → (p3 ∧ p4)) ∨ (p3 ∧ p3)) → (p3 ∨ ((p2 → (p5 → False)) ∨ p3))))) ∨ True) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118531211083898648542423319823 : ((p3 ∨ (p1 ∧ ((p3 ∨ (((True ∨ p4) ∨ p3) ∧ (p1 ∨ (p2 ∧ p3)))) → (((True ∨ p2) → (True ∧ (p1 ∧ p1))) ∨ False)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768463497987929107818194496532 : (((p5 ∧ ((((((p1 ∨ p4) → p2) → (p2 ∧ (p3 ∧ (p4 → p2)))) ∧ (p3 ∧ p3)) ∨ True) ∧ ((p4 ∨ ((p2 → p2) ∨ p5)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245601109259630941182309070940 : ((p3 ∧ False) ∨ ((((((p5 ∧ p4) → p5) → p1) ∨ (((p1 ∧ p1) ∧ (False → p4)) ∧ p1)) → ((p1 ∧ p1) ∧ p4)) ∨ (False → (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351991777311022153245268907551 : (p4 → ((((p2 ∨ ((p2 ∧ p5) ∨ p3)) ∨ p2) ∨ p2) ∨ ((p3 ∨ ((p4 → True) ∧ (((p2 ∧ (p4 ∨ False)) ∧ p2) → (p1 ∧ p3)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164186915916477706544194021539 : ((p5 ∨ ((p5 ∨ ((p1 ∨ ((p1 ∧ p4) ∧ p3)) ∨ ((p1 ∨ p5) ∨ (True ∨ p1)))) ∨ p4)) ∧ ((True ∨ (p2 ∨ (True → p4))) ∧ (p5 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40163380546619122734224855564 : ((((((p4 ∨ ((p3 ∧ p4) ∨ (p1 → True))) → p3) ∧ (((((p2 → p3) ∨ (p5 ∧ p4)) ∨ (False ∧ p3)) → p4) → p1)) ∧ False) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112577755793474223769581072045 : ((((p3 → ((p4 ∨ (p5 ∨ (((p3 ∧ ((False ∧ (p1 → (p2 ∨ p1))) ∨ p5)) → p2) → p3))) → (False ∧ p3))) → p3) → p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54436389698654443331296983051 : ((((p1 ∨ (((p5 → p5) ∧ False) ∧ False)) ∨ p5) ∨ ((((False ∧ (False ∧ p5)) ∧ p4) ∨ p2) ∨ (False → (False → ((p5 ∧ False) ∧ p3))))) ∨ p2) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114595888333984413369934171438 : ((((p2 → p4) → (p2 ∧ (p5 → (p1 → (p1 ∨ (False ∧ (p4 ∧ (True ∧ True)))))))) ∧ (p2 ∨ (p5 → (p5 ∧ (p1 ∧ p2))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204319663833573086674480015666 : (((p2 ∧ (True ∧ (p2 ∨ p1))) ∧ p4) ∨ (p4 ∨ (p2 → ((((True ∧ (((p1 → p5) ∧ p3) ∨ False)) ∧ p2) → (False ∧ (p3 ∨ False))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225939525797827830681362492006 : (((p2 ∧ p3) ∨ p1) ∨ ((((p2 ∧ p1) ∨ (((p2 ∧ ((False ∧ (p4 → ((p1 ∧ True) ∨ (p4 ∨ True)))) → p2)) ∧ p3) → False)) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244122572686224775376934443728 : ((True ∧ p4) ∨ ((((p3 ∨ p2) ∨ (p4 ∨ ((p5 ∧ p4) ∨ (((True → p3) → False) → ((True ∧ False) ∨ (p3 → p1)))))) ∨ (p2 → False)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True → p3) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57174242101508301712317145519 : ((((p5 ∧ False) ∨ False) ∨ ((p3 ∨ (p2 ∧ p2)) → (((p5 → ((p2 → (True → ((p3 → p2) → (p2 ∧ p1)))) ∧ False)) ∧ p3) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244090115502985529008532054897 : ((True ∧ p3) ∨ (((p2 → ((p3 → p2) ∧ ((True → p4) → p2))) ∨ (p3 ∨ p1)) → (p5 ∨ (((p1 ∧ (p5 ∧ p1)) ∨ (False → False)) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213122775097746972265577844396 : ((((False → True) ∧ True) ∧ p1) ∨ (p3 ∨ (((((((False → p1) → p1) → True) ∨ p3) ∨ p4) → ((p4 → p2) ∨ ((p2 ∨ False) → True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740443799678624570140958407544 : ((((p1 ∨ p4) ∨ ((((p3 → p1) → p1) ∨ (p4 ∧ ((p2 ∨ (p5 ∧ ((p2 ∨ p1) ∨ p3))) ∨ p2))) ∧ (p2 → ((p5 ∧ p1) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119608837154048331337244435355 : ((p5 → (p3 ∨ (p1 → ((((p5 ∨ (p4 ∨ p2)) ∧ ((False → False) ∨ p1)) → (p5 ∧ (p4 → (p2 ∧ (p5 → p2))))) ∨ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66407745296529761754623291109 : ((p5 ∨ (p1 → (p3 ∧ ((((False → (False ∧ ((True → p1) ∧ True))) ∨ (False ∨ (((False ∨ p5) → p4) ∧ (p5 ∨ p5)))) ∧ True) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313067926982026455714210547091 : (p3 ∨ (((p5 → (((((p5 → (False ∨ (True ∧ False))) ∧ (p2 → ((p3 → p1) ∨ p3))) ∨ ((p5 ∧ False) → True)) → p5) → p3)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49336736733892650248755422283 : (((True → (((p2 → p2) ∧ (p4 ∨ (p1 ∧ (((False ∨ (((p3 → True) ∧ True) ∨ True)) ∧ p1) ∨ p5)))) → p4)) ∨ (p3 → (False ∨ True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173631964296850658378030666351 : (((p1 → (p5 ∧ (False → (False ∨ (((p1 ∧ (p2 → p1)) ∨ True) ∧ p5))))) ∧ p4) → (((False ∧ (p1 ∨ p4)) ∨ ((p5 ∨ p2) ∧ p5)) → p5)) := by
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
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h1.left
      let h14 := h1.right
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225223369137817466796743002891 : (((p5 ∧ p1) ∧ p5) ∨ ((p5 ∧ (p1 ∧ (p3 ∧ True))) → ((((((p5 ∧ ((p2 ∨ p1) ∨ p2)) → True) → (p2 ∧ p3)) ∨ False) ∨ False) ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47791993579597472850040939774 : ((((((p4 ∨ ((False ∧ p2) → p3)) ∧ (p4 ∧ ((p1 ∧ p1) → ((p5 ∨ ((p2 → p3) → True)) → p2)))) ∨ p3) → p1) → (p5 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



