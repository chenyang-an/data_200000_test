variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319374168967350781502023514501 : (p4 ∨ (((p1 ∧ p1) ∧ (True ∧ (p3 ∧ (p1 ∧ (True ∨ ((p2 ∨ True) → p1)))))) ∨ (True ∨ ((p3 ∨ (p3 → ((True → p3) ∨ p4))) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148629201760430114314354369312 : (((p3 ∧ (False → (p3 ∨ ((p1 ∨ p1) → (True → p5))))) → (p4 ∨ ((p2 ∧ ((p1 ∧ p5) ∨ p3)) ∧ p3))) ∨ (p4 → (True ∧ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592526520827308118409056425531 : ((((((p2 ∧ p2) → (((p1 → (p1 → (p1 ∧ p4))) → (p1 ∧ False)) ∧ (((p2 → p4) ∧ p3) ∧ (p5 → True)))) → (p4 → p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231049584766560271675895761733 : (((True ∨ p2) ∨ True) → ((((False → False) ∧ (p3 ∨ (((p3 → False) ∨ p5) ∨ p4))) ∨ (p1 → (p1 ∨ p2))) ∨ (p3 ∧ (p4 → (p2 ∧ False))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184666178386309989949512773141 : ((((p1 ∨ False) ∧ ((p3 ∨ p1) ∨ p3)) ∨ ((p1 ∧ p2) ∧ p5)) ∨ ((((True ∧ ((p4 ∧ True) ∧ p3)) ∧ p5) ∨ ((True ∧ p3) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_171588865569063418307692516285 : ((((((p3 ∨ ((True ∨ p5) ∨ p2)) ∧ p3) ∧ False) ∨ ((p1 → False) → p4)) ∨ p1) ∨ (p3 → ((p4 → (False ∨ (p1 ∨ (p2 ∨ p1)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168318723620597924520086523824 : (((False → p5) ∧ (p5 ∧ ((p4 → (((p4 ∨ (p1 → (p1 → p3))) ∧ False) ∧ True)) ∧ p4))) → (((p4 → False) → (p3 ∧ (p1 → p2))) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161462936879572915727419087407 : ((p3 ∧ ((((p1 ∨ p1) ∧ p1) → ((False ∧ ((p5 ∨ True) → p1)) → (p1 → p3))) ∨ (p2 ∧ p3))) → ((((False ∨ p2) → p5) ∧ p4) ∨ p3)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43179214762566879769462873526 : (((((False → True) ∧ ((((p5 ∧ False) ∧ p3) ∧ (((p1 → ((p2 ∨ p5) ∧ ((p3 → p2) ∧ p3))) ∨ p1) ∨ p4)) → False)) ∧ p3) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743327966913741060760482403235 : ((((p5 → False) ∨ ((p5 ∨ p1) ∨ (((p1 ∧ p1) → ((p3 → p4) ∧ ((True ∨ (False ∧ (False → False))) ∧ (False → (p1 ∧ p3))))) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251780136372029057418581476066 : ((p3 → p4) ∨ ((((p5 ∨ False) ∨ (((p5 ∧ False) ∨ (p4 ∨ (True ∨ ((((False → p1) ∨ p1) ∨ p1) ∧ p4)))) ∧ p4)) ∨ (False ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_399863454421500826897533521982 : ((((p3 → (p5 → (((p3 → ((p2 ∨ p2) → p4)) ∧ p1) → (True → (((p2 ∧ p3) ∨ (p2 ∧ (p1 ∧ (p4 → False)))) ∨ True))))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_382791897235915970509670475533 : ((((((p2 → True) ∧ (((p2 ∨ (p4 → (p1 ∨ (p1 ∧ True)))) ∨ (p4 ∧ ((True → p2) → (p1 ∨ (p5 ∨ p1))))) ∧ p5)) ∨ p3) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_58487430856783518713154590461 : (((p4 ∨ p1) ∧ ((p5 ∧ p2) ∧ (((p2 → ((((p2 ∨ ((((True → p2) ∧ p1) ∧ True) ∨ p4)) → p3) → p3) ∧ True)) ∨ p5) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345468215879223563281650929336 : (p3 → (((p4 ∨ ((((p5 ∨ p5) → p4) ∨ ((p1 → (p3 → True)) → ((p1 ∧ p5) → (p2 → False)))) ∨ True)) ∧ (p4 ∨ (p4 ∨ False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317970841462595327772087167722 : (p4 ∨ ((p1 → ((((p3 ∧ ((((False ∧ True) ∧ (True ∧ True)) ∨ p3) ∨ (False → p2))) ∧ (p1 ∧ ((p3 → False) ∨ p3))) ∧ True) ∨ p1)) ∨ p1)) := by
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
theorem thm_5_vars_300407602557525393039226695417 : (False ∨ ((p1 ∨ ((p4 ∨ (p5 ∧ (p5 ∧ (p4 ∧ (False ∧ True))))) ∧ (((False ∧ (p1 ∧ (True ∨ p5))) → p2) → p2))) ∨ ((False ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171839443629394835662089135139 : ((((False → (p4 ∨ p3)) → (p3 ∨ ((True → p3) ∧ ((False ∨ p3) → p5)))) → p3) ∨ (p5 ∧ ((((p1 ∨ (p2 ∨ p5)) ∨ p3) ∨ p4) ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (p4 ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183879325848553000737690706509 : (((((p5 ∧ False) ∨ False) ∨ (False ∨ ((True ∨ True) ∨ p5))) ∧ p1) ∨ ((p1 ∧ (p5 → ((((p1 → p1) → False) → (p4 ∨ False)) ∨ p4))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213093036366254173957700535213 : ((((p5 ∧ p5) ∧ p1) ∧ p4) ∨ (((p1 ∨ ((p1 → (p4 ∧ (True ∧ p1))) ∧ p5)) ∨ (p2 → ((p1 → p1) ∨ (p5 ∧ p4)))) ∨ (p3 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354842109840575274552705979580 : (p5 → (((p4 → p5) ∧ ((p2 ∨ True) ∧ ((p5 ∧ p1) ∨ (p2 ∨ ((((p3 ∧ (True → (p4 ∧ p5))) ∧ p1) ∧ (p4 ∧ False)) ∧ p3))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133873990927194154155860094661 : (((p4 ∧ ((((True → ((False → (p5 ∧ p5)) ∨ (((p2 ∧ p4) ∨ False) → p1))) ∨ False) → (p2 → p5)) ∨ p3)) ∧ p2) ∨ (True ∧ (True ∨ p4))) := by
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
theorem thm_5_vars_3282598601757508378029344429 : ((p4 → p2) ∨ (((p2 → ((p1 → (p1 ∨ False)) ∧ ((p3 ∧ (False ∧ p3)) ∧ ((p2 → p5) → p1)))) ∧ (p4 ∨ p2)) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158433041202223021898537289053 : (((False ∨ p2) ∨ (False ∧ ((p4 → (True ∨ ((p5 → p4) ∧ p4))) → ((False ∨ (p1 → True)) ∨ p4)))) ∨ (p1 ∨ ((False → p3) ∨ (p5 ∧ False)))) := by
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
theorem thm_5_vars_115080949053136753304518973985 : (((p3 ∧ ((p5 ∧ (((p4 → p5) ∧ (p1 → p1)) ∨ p2)) ∨ p5)) ∨ (p2 → (((p1 ∧ (False ∧ p1)) → p4) ∨ (p1 ∧ False)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191296931252862413843445828115 : (((p1 → True) ∧ (((False ∨ (True ∧ p4)) → p1) → False)) ∨ (p2 → ((p3 ∨ (((False ∧ ((p4 → p4) ∨ p2)) ∨ False) ∨ p2)) ∨ (p3 ∨ False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149957979186154102166191474406 : ((p4 ∨ (((((((p5 ∨ ((p2 ∧ p1) → p5)) ∨ p5) → (p3 ∨ True)) → p3) → p1) ∨ (True ∧ True)) ∨ p2)) ∨ ((True ∧ (p2 ∧ p2)) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_137716131853878349616490989303 : ((p1 ∨ (((False ∨ p4) ∧ True) ∨ (p5 → (((p4 ∧ p5) ∧ (p3 → p3)) → (((p3 ∨ (p3 ∨ p5)) ∨ p2) ∨ p5))))) ∨ ((p3 ∧ False) ∧ p1)) := by
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
theorem thm_5_vars_809793715375229757076466263618 : (((p5 → (((p1 ∧ p4) ∨ (p2 ∧ (((True ∨ (p5 → (p2 → ((False ∧ True) → ((p4 ∧ p3) ∨ p1))))) ∧ p3) ∧ p3))) ∨ (p1 ∨ p5))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173092447404205531942512948567 : ((p1 ∨ (((p5 → True) → True) → (False ∨ (True → ((p1 ∨ False) ∨ (p1 ∨ p3)))))) ∨ (((p2 ∧ p4) → (p3 → (True → (p5 → True)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164707431662376521173076432521 : ((((p4 ∧ ((False ∧ p1) ∨ ((((True ∨ p3) → (p1 ∧ p4)) → False) → p4))) ∨ True) ∨ True) ∨ (((((p1 → p3) → p4) ∧ p1) → p4) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209215589274043973597647081145 : ((p4 ∨ (p5 ∨ (p3 ∧ (p5 → p4)))) → ((True → (p4 ∨ p5)) ∨ ((((False ∧ False) ∧ p3) ∨ (p3 ∨ (False ∧ (p1 → True)))) ∨ (False ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678390646652268257186674898808 : (((((p1 ∨ ((p1 → (p2 ∧ False)) ∨ p2)) → (p2 → ((p5 ∧ (p5 ∧ (p5 ∨ (p5 ∨ p3)))) ∧ p4))) ∨ (False ∨ (p5 → (True → p5)))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201235750866350913653383770834 : ((p2 → (p2 ∨ (p1 ∨ ((p5 ∧ p4) → p3)))) → ((p4 → p3) ∨ ((p3 → ((p3 ∧ (True ∨ (True → p3))) → p2)) ∨ (True ∨ (True → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41150868871197793034866988452 : (((((p5 → (p5 → p4)) → ((p4 → ((p5 ∧ p2) → (((p2 ∨ p3) ∨ (True ∨ p5)) → p2))) ∧ False)) ∨ (p2 ∨ (True ∧ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345528819980447042641231266721 : (p3 → (((((p2 ∧ False) → p2) → ((p1 ∧ False) ∧ (True ∨ p5))) ∨ (True → (False ∨ (((p3 ∨ (p4 ∧ p2)) ∨ True) ∨ (p5 ∨ p5))))) ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62135367542947671023378977314 : ((p2 ∧ (p4 ∨ (p5 → ((((p4 → p3) ∨ ((((p4 ∧ (p4 → (False ∧ ((p2 → p5) ∨ p3)))) ∧ p4) ∧ p3) ∨ p2)) ∧ p4) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260090114534851899042513072278 : ((p2 → False) → (p2 → (False ∨ ((p5 ∧ (p5 ∨ True)) → (((p5 ∨ False) → p3) → ((False → ((p4 → (p2 → (p2 → p5))) → p2)) → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64914091987231342894119076814 : ((p2 ∨ ((p3 → (((p1 ∨ p1) ∧ ((((True ∧ (p5 ∧ p1)) ∧ False) ∧ p3) ∨ p4)) → (p3 ∨ p5))) → (p5 ∨ ((p1 → p2) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_467958360017938940993590003564 : (((((p5 → p4) → (((p3 ∧ False) → (False ∧ ((p1 ∧ p3) ∨ p2))) → p2)) ∨ (p1 → (p4 → (p4 ∨ ((True ∧ p5) ∧ (True ∧ p5)))))) ∧ True) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68911963367174834446759858768 : ((p4 → (False ∨ ((False → (False → (p4 → (p2 ∨ (True ∨ p2))))) ∧ ((p2 ∧ ((((p5 ∧ p1) ∨ p1) ∧ p5) ∨ (p5 → p4))) ∨ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134297116578211581022605208642 : ((((True ∨ p4) → (False ∧ (((((p4 → (False → (p3 → False))) ∧ (p2 ∧ False)) ∨ p3) ∨ False) ∧ (p3 ∧ p5)))) ∨ False) ∨ (False → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245220246060144274685627283891 : ((p2 ∧ p1) ∨ ((((p1 ∨ ((((False ∨ p1) ∨ p5) ∨ p5) ∨ (((p4 → (p3 ∨ True)) → p2) → p4))) → (p4 ∧ (p1 ∨ True))) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60489375857957937235136582805 : ((True ∧ ((((p3 → (p1 ∨ ((p2 ∨ p1) ∧ p1))) → ((p4 ∨ False) ∧ ((p5 ∧ ((p4 ∧ (p2 → p4)) ∧ p2)) ∧ True))) → p5) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148860648181941187822991674907 : (((p1 ∨ (p4 ∧ (False ∨ p1))) ∧ ((True ∧ (p3 ∨ ((True ∨ p4) ∨ (True ∨ p4)))) → ((p2 ∨ False) ∧ p1))) ∨ (((p3 ∧ p5) → p3) ∨ p4)) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802418353671661664997006209829 : (((p2 → (p1 ∨ (((((p5 ∧ (((((p1 ∨ True) ∧ p4) ∧ p4) ∨ p2) ∧ (p3 ∧ ((p4 ∨ p1) ∨ True)))) ∧ p2) ∨ p2) ∧ p2) ∨ False))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207593273196327091427506365740 : (((((p1 ∨ p1) ∧ p1) → True) → False) → (p5 ∧ (p1 ∨ (p3 → ((False → (False ∧ ((((True → p5) ∨ p3) ∨ p3) ∧ (p5 ∧ p1)))) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p1) ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p1 ∨ p1) ∧ p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192314152661413488084219879983 : (((p3 ∧ ((False ∨ (p5 ∧ (p3 ∨ True))) ∧ p5)) ∧ p1) → (((p1 → (p2 ∨ p4)) ∨ (((False ∧ p2) ∨ ((True → p1) ∧ p2)) ∨ p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141139387159487780507252593430 : ((((((p5 ∧ p2) → p2) ∨ p3) → p3) ∧ ((((False ∧ p1) ∨ False) ∨ (True → ((p1 ∨ True) ∧ p2))) ∧ (False → p3))) → ((False ∨ p2) ∨ p1)) := by
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
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699172149723331995299206104067 : ((((p1 → ((p5 ∧ (p5 → p3)) ∧ ((p5 ∨ (False ∧ True)) ∨ False))) ∨ (((((p2 ∧ (True ∨ (p1 → False))) ∧ p1) ∧ p5) ∨ False) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254779946671921515226784624381 : ((p3 ∧ p4) → (((p2 ∧ p5) → (((True ∨ (p5 ∨ p1)) ∧ True) → p4)) → (((((p2 → False) ∧ True) ∨ p3) ∨ (False ∧ p1)) ∨ (False ∨ p4)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712675828953045776168459151770 : (((((p3 ∨ p1) ∧ ((p4 ∨ p2) ∧ p3)) ∨ (((True ∨ (((p2 → p5) ∧ ((True ∨ p5) → (p5 ∨ p1))) ∧ True)) → (p4 ∨ p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164793697632614786865448319611 : (((((p2 ∨ (False ∨ True)) → False) → (((p1 ∧ p5) ∧ ((p2 ∧ p5) ∧ False)) ∨ p4)) ∨ p5) ∨ ((p4 ∧ (p5 → p2)) ∧ (p5 ∧ (True ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ (False ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98979404491369472156419354593 : ((True → ((p1 → (True ∧ ((((p5 ∨ (p1 ∨ p5)) ∧ ((p4 ∧ p1) ∧ False)) → p4) ∨ False))) ∧ ((False ∧ (p5 ∧ (False → True))) ∧ p2))) → p4) := by
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
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655441449123366789921985332350 : ((((((p1 ∨ p2) → (p4 → ((False ∧ (((True ∧ True) ∧ (p5 ∨ p3)) ∧ p2)) ∨ (p1 → (p1 ∨ p3))))) ∨ (p5 → p4)) ∨ (True → False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41698201155794497924382139612 : (((((False ∨ (False → (p1 ∨ False))) → p5) → (((((p3 → p2) ∧ (True ∨ (p3 → p1))) ∧ (False ∨ False)) ∧ p5) ∨ (p2 → True))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181296138144542778018575908063 : ((p5 ∧ ((True → ((False ∨ p1) ∨ p3)) ∨ ((False → p1) → (False ∨ p5)))) → ((p5 → ((False ∧ (p3 → False)) ∨ (p1 → (p1 → p1)))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171801604815824549712626256376 : ((((True ∧ ((p4 → (p2 ∨ (p2 ∨ True))) ∨ p1)) ∨ (p5 ∧ (p3 ∧ p3))) → p3) ∨ (False → (((p1 ∨ False) ∨ p1) ∧ ((True → p4) ∨ p4)))) := by
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
theorem thm_5_vars_40627381093894903338424548511 : (((((((((p5 ∨ p3) ∨ (((p5 → p5) → False) ∨ (p1 → (p3 ∧ p2)))) → (p1 ∨ p4)) ∨ (True ∨ p1)) ∨ False) → p5) → p2) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312099344714983281467074574777 : (p2 ∨ (p5 ∨ (p5 → ((((((True ∧ (p2 ∨ (p1 ∧ True))) ∨ (p2 ∨ p2)) → (True ∧ p1)) ∧ p1) → (p3 ∨ ((p2 → False) ∨ p3))) ∨ True)))) := by
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
theorem thm_5_vars_63222288572333977129321410174 : ((p5 ∧ (((False ∨ ((p4 → (p2 → (p5 ∨ p4))) → (True ∨ (p4 → p2)))) ∨ (False → p4)) → (p4 → ((True ∧ (p2 ∨ p1)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322377781149616767108493573418 : (p5 ∨ ((((p5 ∨ (p4 ∨ p2)) ∨ ((True ∨ p1) → (p5 → (True → (True ∧ (p5 → (False ∨ p1))))))) → (((p3 → p3) ∨ p1) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54633124749506286974113480714 : (((((p3 → p1) ∨ ((p4 → p4) ∧ p4)) ∧ True) → ((p4 → p3) ∨ ((((False ∧ (p3 ∨ p4)) → True) ∨ (p3 → (p1 → p2))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633328352455757323355085682552 : ((((((((False → (p4 ∧ (True → (p2 ∧ ((False → (False ∧ p3)) ∧ ((p2 → p3) ∧ False)))))) ∨ True) ∨ True) ∨ p3) ∨ (p3 ∧ False)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672737663456408185521824875979 : ((((((p4 → (p3 ∨ (p1 → (p5 ∨ ((((True ∧ False) ∨ False) → p1) ∧ p3))))) → (False → p2)) → (p3 → p1)) → (True ∧ (p2 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133627913854755309801908819457 : (((((p5 ∨ p4) → (False ∨ (((p1 ∨ True) ∨ (True ∨ (p1 → (p2 ∨ p2)))) ∧ ((p4 → False) → p2)))) → p3) ∧ p5) ∨ (p4 → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616581456354745166105793192199 : ((((((p3 ∨ ((True ∧ (p3 ∧ p1)) ∧ False)) ∧ (p3 → p5)) ∧ (((p4 → False) → (((p4 ∨ p2) ∨ p1) → p3)) → (False ∨ True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_619848993877680624142938284327 : (((((p4 ∨ True) ∧ ((p1 ∨ ((False ∨ p4) ∨ ((p1 ∧ (p1 ∧ (p5 ∧ (p5 ∧ (p4 ∧ (p2 ∧ True)))))) ∨ False))) ∨ (True ∨ p5))) ∨ p2) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158881546398536762075672399974 : ((False ∨ (p3 ∧ (((p4 → ((p1 ∨ p3) → ((p2 → p5) ∨ False))) → (p1 ∨ p2)) ∨ (p2 → True)))) ∨ ((p1 ∨ (p2 ∧ p4)) ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156612153183714798379579762191 : ((((False ∨ ((p4 → ((p3 ∧ (((p5 ∨ (p3 ∧ p1)) → p1) → p3)) ∨ False)) ∧ p2)) ∧ p2) ∧ p3) ∨ (((p1 ∨ True) ∨ p2) ∨ (p1 ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47593506107052390632004602357 : (((p3 → (((p5 ∨ ((True ∧ p1) ∧ ((((True ∨ p4) → p2) → ((p4 ∧ p2) ∧ (p1 ∨ True))) ∧ p1))) ∨ True) ∧ p3)) ∨ (p4 ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51607152689678798449072223276 : (((p5 → (p1 ∨ (p1 → (((p1 ∧ ((False ∨ (True ∧ p2)) ∧ (p5 ∧ True))) ∧ False) ∧ True)))) → (True ∧ (p2 → ((p1 → p5) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156677965604685990850832425858 : (((((True → ((True → (False ∨ p2)) ∧ (p3 → p4))) → (p5 ∧ (False ∧ p4))) ∨ (p4 ∨ p3)) ∧ True) ∨ ((p3 → (p2 → False)) → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493670075890289804302678371014 : (((((p4 ∨ (p5 ∨ p5)) ∧ p4) → (p5 ∨ (((p5 ∧ p5) ∧ p5) ∨ (p1 ∨ (((p3 ∨ True) ∨ (p5 → ((p4 → p5) ∨ False))) ∨ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172812892381046100828271994463 : ((True ∧ ((True ∨ ((p2 → p5) ∨ ((p1 → False) ∧ (p4 ∨ (p5 ∧ False))))) → p2)) ∨ ((True ∨ (p4 ∨ (p4 ∨ ((p5 ∨ p1) → p2)))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336090767971526881888988990985 : (p1 → ((((False ∧ True) ∧ ((((False ∧ p5) → p4) → (p2 ∧ (((p5 ∧ True) ∧ (True → p4)) ∧ ((p4 ∨ p2) → p3)))) ∧ p5)) ∧ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166288952298373840262101776081 : ((p4 ∧ (((((p4 ∨ False) ∧ (p4 ∨ (True → p2))) ∧ p2) ∧ False) ∨ (p4 → (True → p5)))) ∨ (((p5 ∧ p3) ∨ True) ∨ (p4 → (p4 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625808316937688716747380400978 : ((((p1 → (p3 ∨ ((((False ∧ p1) ∧ True) ∧ ((False ∧ (p2 ∨ (False → p4))) ∨ False)) ∨ (((p2 ∧ (p4 ∧ p3)) → p1) ∧ True)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_249179998050340225352037157187 : ((p4 ∨ p3) ∨ (((((p5 ∧ p4) → p4) → ((p1 → p5) → (p2 ∨ ((p5 ∨ p5) ∧ ((True ∨ (False ∨ p1)) → p4))))) ∨ False) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111695464365017928359575690446 : (((((((p5 ∧ p5) ∧ (p5 ∧ p2)) → ((p2 ∨ p1) → ((p4 → (True ∧ p4)) ∨ (p4 ∧ (True ∨ p2))))) → p5) → p4) ∨ p2) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162885826998554485028625102170 : (((p3 ∧ (p4 → (p5 ∧ (((False ∨ (p2 ∨ p5)) → (p5 → p5)) ∨ False)))) ∨ (False → False)) ∧ (False ∨ (((p3 ∨ (p5 ∧ p4)) ∧ p1) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115428624921247773860117225695 : ((((False ∨ (p3 ∧ (p1 ∨ (p3 ∧ p5)))) ∨ p4) ∨ ((((((p5 ∧ p5) ∨ True) ∧ p4) ∨ p5) → (p4 → False)) ∧ (p4 → True))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305211450335491007784964111611 : (p1 ∨ (((((p5 ∨ ((p1 ∨ p3) ∧ p1)) → (p4 ∧ p2)) ∧ (((p2 → p3) ∧ (p3 ∧ True)) ∧ True)) → p2) → ((True → False) → (p3 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192809974538647841702780030883 : (((False → ((p2 ∨ True) ∨ (p3 ∧ (p4 ∨ True)))) → p3) → ((((p5 ∧ p2) ∨ p3) ∨ (False ∧ ((p5 → True) → (p4 → True)))) ∨ (p2 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → ((p2 ∨ True) ∨ (p3 ∧ (p4 ∨ True)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171796617567529249527667755780 : ((((((p5 → p5) ∧ p5) ∧ ((True → True) → True)) ∧ (True → (p5 ∧ False))) → False) ∨ ((((p1 → True) ∧ (p5 → True)) ∨ True) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47486990816495977699515180558 : (((False ∨ ((((p3 ∨ True) → p2) ∨ (p1 ∨ (p2 ∧ (p3 ∧ ((p3 ∧ (p5 ∨ (p2 ∨ p1))) ∧ p1))))) → (p2 → False))) ∨ (p3 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47509478786335354821412476410 : (((p2 ∨ ((p5 ∨ (p1 ∨ (((p3 ∧ ((p2 ∧ False) ∧ p5)) → p1) → ((p5 → True) → p5)))) ∨ ((False → True) → p1))) ∨ (False → p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184522465083388203399958065867 : (((p4 ∨ ((False ∨ (p3 ∧ p2)) ∧ (p3 ∧ p1))) ∨ (False ∨ p3)) ∨ ((p1 → ((p2 ∧ p4) ∨ (p1 ∨ p4))) ∨ (p5 ∨ (p3 ∨ (p3 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806700354645584322207164238792 : (((p4 → ((((((True → p5) ∨ (p2 ∨ False)) ∧ p5) ∧ (((p3 → p5) ∨ (p2 ∧ (p5 → False))) ∧ (p5 ∨ p2))) ∨ p5) ∧ (p1 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52097213779501643754139435164 : ((((((p4 → p3) ∨ p5) ∨ (((p4 ∧ True) → ((p3 ∧ p5) → p3)) ∧ True)) ∨ p1) → ((((p5 ∨ p3) ∨ (p2 → p1)) → False) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208781391273576502926152652625 : ((p2 ∧ ((p2 ∨ False) → (p3 → p5))) → ((((p1 ∧ ((((p1 → True) ∨ False) ∧ p5) ∨ ((p3 ∨ p3) ∧ p5))) → p4) ∧ (p3 ∧ p1)) ∨ True)) := by
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
theorem thm_5_vars_39350235991302554427004726516 : (((p2 ∧ (p1 → ((False ∧ False) ∧ (False ∨ (p4 ∨ (p4 → (True ∨ (((True ∧ True) → (((p2 → p4) ∧ p3) → p2)) → True)))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355577099444629741292111058089 : (p5 → ((((p2 → (p1 ∧ p1)) → ((((p2 ∨ (False ∧ (p5 → p4))) ∧ p1) → p3) ∨ True)) → (((p4 → p1) → False) ∨ p3)) ∨ (p3 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53650477900604972873546439904 : (((((p4 ∧ False) ∨ p5) → (p4 ∨ ((False → p3) ∨ p2))) ∧ (p1 ∨ ((p2 ∧ (p5 ∨ p4)) → ((False ∧ p1) ∨ ((True → p2) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50970908224951836635732870267 : (((((p4 ∨ (False ∧ p4)) → p2) → (((p1 → p3) ∧ p2) ∨ ((p4 ∧ p2) ∧ (p4 ∨ p2)))) ∧ (((False → (p5 → p3)) ∧ p1) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53252025098764235476530911792 : ((((p4 → False) ∧ ((p3 ∨ (p1 ∧ ((p1 ∧ False) ∧ True))) → False)) ∨ ((p5 ∧ p3) ∨ (((((True ∧ p5) → True) → False) ∨ p4) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607215110761892447620003801078 : ((((((p2 ∧ (p5 ∨ (p5 ∨ p2))) ∧ (p2 ∧ ((((p3 ∧ p5) → (p1 ∧ (p5 ∨ (p2 ∧ p3)))) ∨ (False ∨ p3)) ∨ p3))) ∧ p2) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166329540875499535741091585867 : ((p5 ∧ ((p1 ∧ p4) ∨ (p4 ∨ ((True → ((p5 ∨ p4) → True)) ∧ (p3 → (p2 ∧ p5)))))) ∨ ((p3 ∨ True) ∨ ((p3 ∨ (p2 → True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116718558963630900574918414270 : (((p2 ∧ p2) ∨ (((((p2 ∨ (((False ∨ p5) → p3) ∧ p1)) ∧ ((p5 → p3) ∨ True)) → p3) ∧ ((p4 ∨ p4) ∧ p4)) → False)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148368957502825570594544765706 : (((((((p5 → p3) → (p5 ∧ p3)) ∧ (p5 ∧ (p1 ∧ p3))) ∨ True) ∨ p2) ∨ (False ∨ (False ∧ (True → p1)))) ∨ (((False ∨ True) ∨ p5) ∧ p2)) := by
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



