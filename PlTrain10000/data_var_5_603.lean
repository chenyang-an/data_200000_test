variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117850519269887562470913269924 : ((p4 ∧ (p5 → ((p4 ∧ (p1 ∧ (p1 → (((((p2 → True) ∨ (p4 → (p3 ∧ p4))) → (p5 ∧ p1)) ∨ p2) ∧ p3)))) ∨ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704365961018988857142780576301 : (((((True ∨ (p3 → (True ∧ p1))) → ((p2 ∨ p4) ∨ p2)) → (False ∧ ((True → (True → p3)) ∨ (((False ∧ p2) → (p2 → False)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66160708502604781204920818218 : ((p5 ∨ ((((p3 → ((p1 → p1) ∨ p3)) ∧ (p2 ∧ p3)) → ((p5 → p1) ∨ (((True ∧ p1) ∨ p1) → p2))) ∧ (False → (True ∨ p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689976691485788481580327990517 : ((((p1 ∧ (((p4 ∨ p2) → (((p3 ∨ p2) ∨ (p5 ∨ (p5 → False))) ∨ True)) ∧ p1)) ∨ (p4 → (((p2 → (p2 → p2)) ∨ p3) → p4))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_42377371550826087465242347053 : (((p4 ∧ (((p1 ∨ False) ∧ (False ∨ (((p1 → p5) ∧ (p5 ∨ (p1 ∨ ((False → (False ∨ (p4 → False))) ∧ p2)))) ∨ p5))) → p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229115256034988611011817544928 : ((True → (p1 ∧ True)) ∨ ((((p1 ∨ (p3 ∨ p1)) → (p3 ∧ (False ∧ p3))) ∨ ((p4 ∧ False) → p3)) ∨ (p3 → ((p1 → p2) ∧ (p5 ∨ False))))) := by
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
theorem thm_5_vars_184244187312372160586812256270 : ((((((p4 → p2) ∨ True) → ((p3 → p1) ∧ p4)) → p2) → p1) ∨ ((p1 → (((p3 ∧ p2) → ((p5 ∧ (True ∧ p5)) → p3)) → True)) ∨ p2)) := by
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
theorem thm_5_vars_597236107531189087152399001934 : ((((((True → False) ∧ (p5 ∧ p1)) ∧ (((True ∧ ((((p2 → (True ∨ False)) → p4) ∧ p4) → False)) → p5) ∨ ((False ∨ p2) → p1))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688674444905977067039157798 : ((((((True ∧ True) → p4) ∨ p1) ∨ (((p2 ∨ p5) → (False ∧ p3)) ∨ False)) → ((((p5 ∧ p3) ∨ p2) ∨ p2) ∨ (True ∧ True))) ∨ p1) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
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
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54056929598504521625527611713 : ((((p1 ∧ ((p3 → p2) ∨ p5)) → ((p4 ∧ p5) → p5)) → (p4 ∧ ((False ∧ (((p1 ∨ True) ∨ (True → (False ∨ p5))) ∧ p2)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784386792023374216103578685849 : (((p3 ∨ (p3 ∧ (((False ∨ True) ∧ p3) ∧ ((p4 → (p3 → (p1 → (False ∧ (True ∧ (p1 → (p1 → ((p5 ∨ p4) ∧ p5)))))))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179625981182400853791558150549 : ((p4 → (((p4 ∧ (p2 ∧ p1)) ∨ (p4 ∨ p2)) ∧ (True ∧ (p2 ∧ p4)))) ∨ ((((p2 ∨ ((p1 → (p3 → p3)) ∧ False)) ∧ p3) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105142088763922953785179518828 : ((((p4 ∨ (p4 ∧ (p4 ∧ (True ∨ p4)))) ∧ (((((p2 ∧ p3) → p4) ∨ p2) ∨ (p3 ∧ p4)) ∧ True)) ∨ (p1 → (True ∨ p3))) ∧ (p5 → p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159055809922040301266536702764 : ((p5 ∨ ((((False ∨ p3) ∨ True) ∨ (True ∧ (p5 ∨ (False ∨ p2)))) ∧ (((p5 ∨ p3) ∧ True) ∨ False))) ∨ (p1 ∨ ((p4 → False) → (False ∨ True)))) := by
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
theorem thm_5_vars_139913700806687197253689605472 : (((((p5 ∧ (p3 ∧ True)) ∨ (True → (p2 ∧ (False ∨ (p1 → p2))))) ∧ (True → (False ∧ (False ∨ p4)))) ∧ (p1 → p1)) → ((p5 ∨ p4) ∧ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_890702650122707407562866850911 : ((((False ∨ ((p4 ∧ (p4 → ((p5 ∧ p3) ∨ p2))) ∨ (((False ∨ (p5 ∨ (((False → p2) → p2) → p3))) → True) ∨ p1))) → (p4 ∨ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ ((p4 ∧ (p4 → ((p5 ∧ p3) ∨ p2))) ∨ (((False ∨ (p5 ∨ (((False → p2) → p2) → p3))) → True) ∨ p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721241599355737691028400482040 : (((((p1 ∨ True) → (p2 ∨ True)) → (p3 ∨ (p1 → ((p4 ∨ ((p1 → p3) ∧ (((p1 ∨ p4) ∨ p1) ∨ p1))) ∨ ((p1 ∨ True) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208149347707419092596087675706 : ((((p5 ∨ p3) → p5) → (p1 ∨ True)) → (((p3 ∨ p1) → (p2 ∧ (p5 ∧ p4))) ∨ (False ∨ (((p4 ∧ ((p4 ∧ False) ∨ p5)) → False) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340515402747037788815105476555 : (p2 → ((((p3 → (p1 ∨ p2)) ∨ False) → (((p3 ∨ p1) ∧ ((((((p3 ∨ (p3 → p5)) ∨ True) → True) ∨ p3) ∧ p4) → p5)) ∨ True)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699049144458203277668482482160 : ((((p2 ∨ ((False ∨ True) → (p5 → ((p1 ∨ p1) ∧ (p3 ∧ p1))))) ∨ ((p2 ∧ ((p3 ∧ (True ∨ p2)) ∨ (False → (True ∨ True)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199180736489100844687703319969 : (((p1 ∧ (False → (p3 ∧ (p4 ∧ p3)))) ∧ True) → (p2 → (((True ∨ p3) → ((p2 ∨ False) ∧ (p5 ∨ p3))) ∨ ((p2 → p4) ∨ (True → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319680062237518909767788593042 : (p4 ∨ (((p4 → False) → (p5 → ((p5 → p2) ∧ p4))) → (p5 → (((((False ∧ p3) ∨ (True → p5)) → False) → (p4 ∨ p2)) ∧ (True ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ p3) ∨ (True → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318847122228348353866284199638 : (p4 ∨ ((((((True → (True → False)) → p2) ∨ p5) ∧ (p2 ∧ ((p4 ∧ ((p4 → False) → p1)) ∧ (True ∧ p3)))) ∧ p3) ∨ ((p4 → False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135497557660550908061267170041 : (((p2 ∧ (True ∧ (p1 → (((p3 ∧ True) ∨ (((p5 → (p4 → False)) → p3) ∧ p2)) ∧ p3)))) → (p1 ∨ (False ∧ p2))) ∨ (False → (False ∧ p3))) := by
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
theorem thm_5_vars_684500839826035543436523969200 : ((((((True ∧ (p5 → p3)) ∨ (p4 ∨ p5)) ∨ (((p5 ∨ (p5 → p3)) ∧ (p2 → p2)) ∨ p2)) ∨ ((((False ∧ p2) ∨ p4) ∧ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354378999511493787256473694569 : (p5 → (((((p3 ∨ p4) ∧ True) ∧ p1) ∨ ((p2 ∨ (p5 ∧ ((p1 ∨ ((p3 ∧ p4) → (p5 ∨ True))) ∨ (p4 ∨ p2)))) ∨ (p1 ∧ True))) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148812695158714130114895569581 : ((((p3 → (p1 → False)) → (p4 ∧ p3)) → (p1 ∧ (((p1 → False) ∧ False) ∧ ((True ∨ (p2 ∧ p3)) ∨ p5)))) ∨ ((True → (p4 → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197325493921067492854178487514 : ((((p1 ∧ p3) → ((p4 ∨ p3) → True)) → p3) ∨ (((((False → p2) ∨ p3) ∨ (((p3 ∨ p4) ∨ (False ∨ p3)) → True)) ∨ p2) ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41485642221075835974815137437 : ((((p3 ∨ ((p1 → (p1 → False)) ∨ (p2 ∨ (p5 → (p2 ∨ False))))) ∨ (p2 ∧ (True ∧ ((p1 ∨ ((True ∨ p4) ∧ False)) ∨ False)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57026616982030312274285540178 : (((p1 → (p5 ∨ p5)) ∧ ((p1 ∧ p1) ∧ ((((p1 ∨ (((False ∧ True) ∨ p3) → (True ∧ p1))) ∨ p3) → (p2 → (p4 → p1))) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164763158024296828396328653711 : ((((((False → p5) → (p3 → (p5 → (p4 ∧ p2)))) ∧ p2) → (True → (p3 ∨ p4))) ∨ True) ∨ (False ∧ ((p3 → (p3 ∧ (p2 → p3))) → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166436816137176505113353108592 : ((p1 ∨ (p2 → (p3 ∨ ((p1 ∧ ((((p1 ∧ True) ∨ (p2 → False)) ∧ p3) → p1)) ∨ p4)))) ∨ ((p3 → p4) ∨ (p1 ∨ ((p4 → p3) ∨ True)))) := by
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
theorem thm_5_vars_55981766535178880968370548953 : ((((p1 ∧ (p1 ∨ p2)) ∧ p2) ∨ (p1 → (((p5 → p5) → False) → (((((True ∨ False) → p3) ∨ p3) ∨ p2) → ((p2 ∨ True) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186671681478882197238378438960 : ((((p2 ∨ p5) ∨ ((p1 → p1) ∨ p5)) ∧ ((p2 ∨ False) ∨ p3)) → ((((p4 ∧ (p5 → p3)) ∧ True) ∨ ((False → p2) ∧ (p5 → p5))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- False on the left can always be used.
          apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179130822262358271168214325662 : ((p1 ∧ ((p1 → (p5 ∧ (p1 ∧ True))) ∧ (p2 → ((p1 ∧ p4) ∨ True)))) ∨ (((p3 ∧ p4) ∨ p3) ∨ ((p3 → ((p3 ∨ p4) ∨ p5)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342303160054581630633749898558 : (p2 → ((True → (p4 ∨ (p2 ∧ ((p4 ∧ p5) ∧ (((p3 ∧ (p3 ∨ True)) ∨ (True ∧ p2)) ∧ p3))))) ∨ (((p2 ∧ p5) → (p5 ∧ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315688371942309930687406787089 : (p3 ∨ ((p1 ∨ False) ∨ (((p4 ∧ (p3 ∧ p4)) → ((((p1 ∨ (p1 ∨ (True ∧ p2))) ∨ p4) ∨ (p2 → (p1 ∨ False))) → False)) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_752321065528969955776935690100 : (((False ∧ (((p1 ∨ (p5 → ((((p2 ∧ p4) ∨ (p4 ∧ True)) ∨ (((True ∨ (p3 ∧ p2)) ∨ False) ∨ p1)) ∨ (False ∨ False)))) ∧ p4) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45720669450794814883422023554 : (((True → ((((True ∧ p3) ∧ p1) ∧ p4) → (True ∧ (((p2 → p5) ∨ (True ∧ (((p2 ∧ p1) ∨ p3) ∧ p1))) ∨ (p2 ∧ False))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354601362688299086315331729320 : (p5 → (((((p3 ∨ (((p1 ∨ p4) ∧ ((False ∨ ((((p4 → False) ∧ (p5 → p4)) → p3) → p3)) ∧ p3)) ∨ p1)) ∨ p4) ∨ p2) ∨ p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74360917992596616613477935945 : ((((p1 → p1) ∧ ((False → False) → (((p5 ∨ ((p2 → ((p5 ∧ (p2 ∨ p3)) ∧ p5)) ∧ ((True → True) ∧ p4))) ∨ p3) ∧ p2))) ∨ p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → False) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133845240897331260083897675929 : (((True ∧ ((p3 ∨ (True ∨ (True → ((False → p4) ∨ p3)))) → ((p1 → p5) ∧ ((True ∧ (p2 ∨ p4)) → p1)))) ∧ p1) ∨ ((True → False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160301463808274756939608496048 : ((((p3 ∨ (p4 ∧ ((p5 ∨ (False ∧ ((False ∧ False) ∨ p1))) → p5))) ∨ (p1 ∧ p5)) → (p5 → p2)) → (p2 → ((p2 ∧ (p1 → True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165371207043614020332184361117 : (((((((p4 → p3) ∧ p2) ∨ (p2 ∨ (False → p2))) ∧ p1) → p4) ∨ (p5 → (True ∧ False))) ∨ ((p4 → (p4 → (p2 ∨ (p5 ∨ p4)))) ∨ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704880023725939238107950447232 : ((((p2 ∨ ((p3 → p4) → ((p1 ∧ p1) → (p1 → True)))) → ((p4 ∨ (p3 ∨ (False ∧ (((p2 ∧ p3) → p1) → (p5 ∨ True))))) ∨ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58340766165116905894369518643 : (((False ∨ p3) ∧ ((((p3 → p2) → p3) → False) ∧ ((False ∨ False) ∨ (((((p1 ∧ p4) ∧ p5) ∧ (p1 → p2)) ∨ p2) ∨ (False ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338228122134340399371210996777 : (p1 → (((p4 ∧ ((p3 → False) ∨ False)) ∨ p4) ∨ (((p4 → (p1 ∧ (((((p3 → (p1 ∧ p2)) ∨ p4) ∧ p1) ∧ False) ∨ p4))) ∨ False) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658181749491199596716845743168 : ((((p4 ∧ (p4 ∨ ((p1 ∧ (((p5 → p2) ∧ ((((p5 ∧ True) ∧ True) ∧ p2) → ((p4 ∨ p2) → False))) ∧ False)) ∨ p3))) ∨ (p4 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_43627689117680913247151218244 : ((((((p2 → ((((p2 ∧ p5) ∧ p4) ∨ p5) ∨ ((((p1 ∧ True) ∧ p3) ∨ p5) → (p2 ∨ p1)))) → False) ∧ (p5 ∧ True)) → p1) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647335162990859101913954741382 : ((((p4 → ((p3 ∧ ((p3 ∧ (p2 → ((p4 → p5) ∧ ((((False ∨ True) → p2) ∧ p1) → False)))) ∨ p5)) → (p2 → (p3 → p3)))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222204162797936800478382417064 : (((p5 ∨ p4) → True) ∧ (((p5 ∨ (((p1 ∧ (((True ∨ False) ∧ (False ∧ p1)) ∨ (p4 ∧ True))) ∧ True) ∨ (p5 ∨ (p5 → p5)))) ∧ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143415368981214873102520870180 : ((p5 → (p4 ∧ ((((True ∨ p2) ∧ (p3 → p5)) → p4) ∧ ((((p3 ∨ p3) ∨ ((p3 ∧ True) ∨ False)) ∧ p4) → p4)))) → ((p4 ∨ False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184860158374825994697232369900 : ((((p2 ∧ p4) ∨ False) ∧ ((((p3 → p5) ∧ p2) ∧ p2) → False)) ∨ (((p1 ∧ (p4 → ((True → p3) ∨ (True → p3)))) → (True → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200769901495824126978177003448 : ((p4 ∧ (((True → False) ∧ p2) ∧ (p4 ∨ p2))) → ((True ∨ p3) → ((p2 → p2) ∧ ((((p1 ∧ (p1 → p4)) ∧ (p4 ∧ True)) ∧ p1) ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h24.left
    let h26 := h24.right
    -- Conjunctions on the left can always be decomposed.
    let h27 := h25.left
    let h28 := h25.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h1.left
    let h33 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h33.left
    let h35 := h33.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h34.left
    let h37 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h38 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h38
    case inr h39 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111104817446600701562291761287 : ((((p1 ∨ (True ∨ (p3 → ((p5 ∨ p3) → (p2 ∧ p3))))) ∧ ((((False → ((False ∧ p5) ∧ True)) ∨ False) ∨ True) → False)) ∧ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_391372759550422152598399387265 : ((((((p2 ∨ p3) → ((p4 → p4) ∧ p3)) → ((p4 ∨ p5) → ((((p3 ∧ p3) → (True ∨ p1)) → p5) ∨ (p5 → (p3 ∨ p5))))) ∨ p4) ∧ True) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125414466845500411831412252554 : (((p2 ∧ p2) ∧ ((p5 → ((True → ((False ∨ p3) ∨ (True ∨ ((p5 → (p4 ∧ p4)) ∧ (False → p5))))) → (p4 ∧ p1))) → p2)) → (p1 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186262848790144614657024462579 : (((((p4 → (p5 ∧ ((p4 ∨ p5) → p1))) ∨ p3) ∨ p4) → True) → ((((((False → True) ∧ (p3 → p2)) ∨ (True → p2)) ∧ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149158474945064099579032122683 : (((p2 ∨ p3) ∧ ((True ∨ ((p3 ∨ p5) ∧ (p1 → p5))) ∧ ((False ∧ (p5 ∨ False)) ∧ (p3 ∨ (False ∧ p1))))) ∨ (True ∨ (False ∨ (p1 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340912563320689985635406059517 : (p2 → (((p5 ∧ (p5 ∨ (False ∧ (p5 ∧ (p3 → False))))) ∧ ((p5 ∨ False) → (p5 ∨ (p1 ∧ (p1 ∧ ((p5 ∨ p1) ∧ (False → p3))))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218030333573611683868127951478 : (((p1 ∨ False) ∧ (p5 → p1)) → (p4 ∨ ((p4 ∨ ((p3 ∨ ((False → (False ∧ p4)) ∧ (p4 → ((p3 ∧ p3) ∨ p3)))) ∧ (False ∧ p1))) ∨ p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652178394737054292924485311202 : ((((p2 ∧ (((p4 ∨ p2) → (((p1 ∨ False) ∨ ((p1 ∨ p1) ∧ (p2 ∨ (True ∧ p5)))) → (False ∧ (p5 ∧ p1)))) ∧ p2)) ∧ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165697247827167335773403204144 : (((True → ((p1 ∧ (False ∧ False)) → p5)) → (((p1 → p1) ∧ (p5 → (False → p1))) → p1)) ∨ ((p2 → (p5 → ((True ∧ p4) → p4))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776460615566543813390454283083 : (((p1 ∨ (((((p2 ∨ (p2 ∨ (False ∧ p2))) ∧ (p3 → (False ∧ (p4 → (p3 ∨ True))))) ∧ ((p1 ∨ True) → p5)) ∧ (False → False)) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_53129348940606550656730638469 : ((((((p1 ∨ (p1 ∧ ((p1 ∨ p2) ∧ p2))) → p3) → p2) ∧ p2) ∨ (((True ∧ (True ∧ (True ∧ p2))) ∧ (p1 ∧ False)) → (p4 ∧ False))) ∨ p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h12.left
  let h15 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h16 := h15.left
  let h17 := h15.right
  -- Conjunctions on the left can always be decomposed.
  let h18 := h17.left
  let h19 := h17.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h13.left
  let h21 := h13.right
  -- False on the left can always be used.
  apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347370236249071274364078574737 : (p3 → ((((False → p5) → ((p4 ∨ p1) ∧ p3)) ∨ p2) ∨ (((True ∨ ((p1 ∨ True) ∨ (((p5 ∧ p3) → p3) ∨ p4))) ∨ p3) ∧ (p1 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258403300212996413132835428519 : ((p5 ∨ p1) → ((p3 → ((True → p1) → ((p1 → (p5 → (((p4 ∧ (p2 → True)) → True) ∨ p5))) → ((p5 ∨ False) ∧ (p1 ∨ p1))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942788502008044363555433036697 : (((((p1 → (p2 ∨ p4)) → False) ∧ (((((True → (True ∨ False)) ∨ (p2 ∨ (p4 ∧ p2))) ∧ p4) ∧ ((p4 → (p5 → True)) ∨ p4)) ∧ p5)) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p1 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : (p1 → (p2 ∨ p4)) := by
        -- Implications on the right can always be decomposed.
        intro h17
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h16
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h21 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h22 : (p1 → (p2 ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h23
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h24 := h2 h22
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : (p1 → (p2 ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h28 := h2 h26
        -- False on the left can always be used.
        apply False.elim h28
    case inr h29 =>
      -- Conjunctions on the left can always be decomposed.
      let h30 := h29.left
      let h31 := h29.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h32 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h33 : (p1 → (p2 ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h34
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h35 := h2 h33
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h37 : (p1 → (p2 ∨ p4)) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h31
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h39 := h2 h37
        -- False on the left can always be used.
        apply False.elim h39
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53988767733878764683447402621 : (((((p3 ∨ p3) ∧ ((False ∨ p1) ∧ (p3 → p4))) ∨ p5) → (p4 → (p4 → (p3 ∨ (p1 ∧ (p5 ∧ ((p3 ∨ (True ∧ p2)) ∨ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52128536505907956302399961798 : ((((p4 → ((p5 ∧ p4) → (p2 ∨ ((p4 ∨ (p5 → p2)) ∨ (p5 ∨ p3))))) → p5) → (p4 → (((False ∧ p4) ∨ p3) ∧ (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697233440010525889843313136482 : ((((((p3 ∨ True) → p3) → (((p3 ∧ False) → p1) → (True ∧ p3))) ∧ ((p3 ∨ ((((True → p3) → p3) ∧ (p3 ∧ p4)) ∨ True)) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161235587842933991046511236166 : (((p1 ∧ p5) → ((p5 ∨ (((True ∨ False) ∨ True) ∨ ((p1 → ((p2 ∨ False) ∧ p4)) ∨ p2))) ∨ p3)) → (p4 → (((False → p5) ∧ p3) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_588698007415679172583915622937 : (((((p2 ∧ (True ∧ ((p4 ∧ ((p3 ∨ (p4 ∨ ((False ∧ False) ∧ True))) ∨ (p1 ∧ (p3 → ((p4 ∨ p5) → p3))))) ∨ True))) ∨ p5) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112813618524663832193452755724 : ((((False → ((p4 → (p1 ∨ True)) ∧ False)) → (p3 → (p4 ∨ (p4 ∨ ((((False → p2) ∨ False) → p3) ∧ (p4 ∨ p3)))))) → p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213918596579320575565501017079 : (((True → (p3 ∧ p1)) ∨ p5) ∨ (((p1 → (((p1 ∧ (p3 → p2)) → p5) ∧ (False → (True → p5)))) → (p1 ∨ p2)) ∨ (True ∨ (p3 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62394591058210332363190529515 : ((p3 ∧ (((False ∧ (p3 → False)) ∨ (p4 ∨ ((False → p5) → p1))) ∧ (((p4 ∨ (p2 ∨ (False → True))) → (False → False)) ∨ (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356651743556615497917334482858 : (p5 → ((((p4 → (p3 ∧ p1)) ∨ (False → p2)) → p3) → (((True ∨ p1) → (((p5 ∧ (p2 ∨ (False ∨ (p1 ∧ p4)))) → p3) ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116130887093535658851478041473 : (((p1 ∧ (p3 → p1)) ∧ (p4 ∨ (p3 ∨ ((p1 ∧ p2) ∧ ((True → (p5 ∨ p1)) → ((p2 → (p1 ∧ (p5 ∨ p1))) ∨ p5)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57850105682747860549520740250 : (((True ∨ (False ∨ True)) → ((True ∧ ((p1 ∨ ((p1 ∧ False) ∨ (True ∧ ((((True ∧ p3) ∨ p3) → p2) → p3)))) → (p3 ∧ False))) ∨ True)) ∨ p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183944043077260659094683558091 : (((p2 ∨ ((False ∨ ((p3 → p3) ∧ p4)) ∧ (p4 → p3))) ∧ p3) ∨ (False → (((True ∧ (False ∨ p4)) ∨ False) ∧ ((p4 ∧ p3) ∨ (True ∧ True))))) := by
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
theorem thm_5_vars_58000665676176529249140342047 : (((True ∧ True) ∧ ((p5 ∨ ((p3 → ((p4 → p5) ∨ p1)) ∨ (p1 ∨ (False → ((p2 ∧ ((p2 ∨ True) ∧ p5)) ∧ (True ∧ p4)))))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246289379402785767756677762272 : ((p4 ∧ p4) ∨ ((p2 ∨ p4) → ((((True → p2) ∧ (p2 ∨ (((p3 ∧ ((p5 ∨ p4) → p2)) ∨ False) ∧ p5))) ∨ ((p4 → p3) ∨ True)) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3046203974846990600515099763 : ((False → (False ∨ p2)) → ((p5 → True) → (((True ∨ ((((p2 → (p1 ∨ (p2 → False))) ∨ p3) → p3) → p2)) → (False ∨ p3)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((((p2 → (p1 ∨ (p2 → False))) ∨ p3) → p3) → p2)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504099391633549168742507233256 : ((((p2 ∧ (True → p1)) → (((p1 → (p2 ∧ ((True ∨ (p4 → p1)) ∧ (False ∧ p3)))) ∨ (((True ∨ (False → False)) ∧ p5) ∨ p3)) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655968703509419835714833314367 : (((((((p2 ∧ p5) ∨ (((p1 ∧ p1) → (False ∧ p1)) → ((p4 ∧ p1) ∨ p1))) ∧ True) ∨ (((p1 ∨ p4) ∧ p4) ∧ p1)) ∨ (p4 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147960974462302029813667240492 : (((p1 ∨ (p3 ∧ ((p2 ∨ p2) ∧ (((p3 → (p4 ∨ p1)) ∧ ((p1 → p5) → False)) → True)))) ∧ (p2 → p3)) ∨ ((p1 ∨ (p3 ∨ True)) ∨ False)) := by
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
theorem thm_5_vars_61860317293183819552826651898 : ((p2 ∧ (((True ∧ p1) ∨ ((((p5 ∨ p1) ∨ (p3 → (p5 → p3))) ∨ (p3 → p5)) ∨ ((True ∨ p1) ∧ ((False ∧ p3) ∨ p5)))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83745880544548023561469194931 : (((((((True ∧ p1) ∧ p3) → True) ∧ (False ∨ (True ∧ ((False ∧ (p2 ∨ p2)) ∨ True)))) ∨ p1) → (p3 ∧ (False ∨ (False ∧ (p4 ∨ False))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∧ p1) ∧ p3) → True) ∧ (False ∨ (True ∧ ((False ∧ (p2 ∨ p2)) ∨ True)))) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55608135649021130833067666606 : (((p1 → (((p1 ∧ p3) ∧ False) ∧ False)) → (p3 ∨ ((p2 → (((p2 ∨ ((False ∨ p2) ∧ (p3 → (p4 ∧ False)))) → False) → True)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310035510693214933848601086462 : (p2 ∨ (((True → False) ∧ ((p5 → p1) ∨ (p4 → ((True ∧ (p3 ∧ False)) → (p5 ∧ p3))))) ∨ (p3 ∨ (True ∧ (((p2 ∨ p5) → False) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127087220385448729187517039889 : ((False ∨ ((p2 → (p3 ∧ p4)) ∧ (((p1 → (p2 ∨ p3)) ∨ p2) ∧ ((p5 ∧ True) ∧ (((p4 → True) ∧ (p4 ∧ p1)) ∨ p3))))) → (True → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h19 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h20 := h9 h19
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h22 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h23 := h5 h22
          -- We need to get the left conjuct of h23 based on <expert-advice>.
          let h24 := h23.left
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h26 =>
        -- One of the premise coincides with the conclusion.
        exact h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h8.left
      let h29 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h37 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h38 := h5 h37
        -- We need to get the left conjuct of h38 based on <expert-advice>.
        let h39 := h38.left
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h40 =>
        -- One of the premise coincides with the conclusion.
        exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345655169683919313515102873729 : (p3 → ((p5 ∧ ((p2 ∧ (((p4 ∨ p5) → p1) ∨ ((p2 ∧ True) ∧ p3))) ∨ ((p5 → (((p1 ∨ p5) ∧ False) ∨ p4)) ∨ (p1 ∧ False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168601932733301698642614170306 : ((p3 ∧ ((((p5 ∧ True) → ((p3 ∧ True) → (((p3 → p1) ∨ p1) → p5))) ∨ True) ∨ p2)) → (((True → p5) → (p4 → (p2 ∧ p5))) ∨ p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779303168838183857717599169266 : (((p2 ∨ ((p5 ∧ (((p2 → p3) ∨ (p4 → ((p4 → p4) → (p2 ∨ p2)))) ∨ ((((p3 ∧ (p4 ∨ p4)) → False) → True) ∧ p3))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327815631077944438302211592824 : (True → ((((p1 ∨ ((p2 → (p3 ∨ True)) → p4)) ∧ (((((p3 ∨ p4) ∧ (True → (p5 ∨ p4))) ∧ p4) ∨ False) ∧ p5)) → p3) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20239156968041040119714984241 : ((((p4 ∨ (p3 → (p2 ∨ (p5 ∧ p4)))) ∨ ((p2 ∧ p1) → (p3 → False))) ∨ (False → (p1 ∧ (((p4 ∨ True) ∨ False) ∧ (False ∨ p2))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42499678252600915975230647122 : (((False ∨ ((True ∨ (False → (((False ∧ (False ∨ p4)) → (False ∧ ((((p4 → p3) ∨ True) → p4) → p2))) ∧ p3))) → (p2 ∧ True))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42386885593813758063647478149 : (((p4 ∧ (((p4 ∧ (False ∨ (False → ((p4 → True) ∨ p3)))) ∧ p5) ∧ ((p2 → ((p4 ∨ ((p3 ∧ p5) → p3)) → p2)) → p5))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62143106811423630058801437941 : ((p2 ∧ (True → (((p3 → ((p1 ∨ (p2 → p4)) → (p5 → ((p4 ∧ p2) ∧ (p1 → p3))))) ∨ (p3 → p5)) ∧ (p3 → (True → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198641158441135781185274857228 : ((p3 ∨ (((p2 ∨ p1) ∧ False) ∨ (p5 ∧ False))) ∨ (((p3 → ((True → p4) → (p3 ∨ True))) → p2) → ((p2 ∨ p4) ∨ (False → (p2 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



