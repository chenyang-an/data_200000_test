variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66234486197789323919714664460 : ((p5 ∨ ((((p5 → (p5 ∨ p2)) → (True ∧ False)) ∧ p4) → (True ∧ (p1 ∨ (((p2 ∨ True) → ((p2 ∨ p3) → p3)) → (p3 ∨ p1)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136495439361019935983517287319 : ((((p2 ∨ p4) → True) ∧ (p1 ∧ (True ∧ (((False ∨ ((p3 ∧ ((False ∧ p5) ∨ True)) ∨ (False → p4))) → p5) ∨ False)))) ∨ ((p5 ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205048170956577496068912305929 : (((False → ((False → p3) → p3)) → p4) ∨ ((((p5 → p3) → (p2 ∧ p5)) → (p2 → (((p1 → p4) ∨ (p3 → (p5 → p3))) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313168635566562602627509165942 : (p3 ∨ (((p2 → (((True ∧ (p1 → (p2 ∧ p4))) → False) ∨ p1)) ∨ (p4 → (((p2 ∧ (p5 ∧ False)) ∨ True) ∨ (p5 ∧ (p5 ∨ p2))))) ∨ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457985611309666357425310811113 : ((((((True ∨ (p5 ∧ (True ∨ p1))) ∧ p2) → (((True ∧ (p5 ∧ p4)) ∧ p3) ∨ (p3 → p2))) ∨ (True → (p1 ∨ (p3 ∧ (p2 ∧ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305403491702380176907043080412 : (p1 ∨ ((((p2 ∧ (((p5 → p5) ∧ (p1 ∧ (False → True))) → p3)) → False) → (p4 → p3)) ∨ ((True ∧ (p3 ∧ p1)) ∨ ((p3 ∧ p5) → True)))) := by
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
theorem thm_5_vars_164907387607042730800819815200 : ((((((p1 ∨ True) → p4) ∧ ((p4 ∨ p4) ∨ ((True → (p2 ∧ False)) → p3))) ∧ True) → p1) ∨ (True ∨ (p5 ∨ ((p5 ∨ p2) ∧ (p4 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244906684727853431052862378575 : ((p1 ∧ p2) ∨ (p1 → (((True → p4) ∨ (p2 ∧ p4)) ∨ ((p4 → (False ∨ ((p5 ∨ (p5 ∨ ((True ∨ p1) ∧ True))) ∧ (True → p3)))) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315275616579813402215296781012 : (p3 ∨ ((((True ∧ p3) → True) ∧ p2) → (True → (False ∨ (((p4 ∨ (p5 ∨ ((p4 → (False ∧ (p1 ∧ p2))) ∧ (False ∨ False)))) ∧ p3) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174722635240627240530779662052 : ((((p3 ∨ p5) ∧ p4) → ((p3 ∧ True) ∧ (((False ∧ p5) ∨ (p3 ∧ p2)) ∨ p3))) → (((p5 → (p1 → False)) ∧ (p4 ∨ p1)) ∨ (p5 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681199915013130756450514626788 : ((((p3 ∧ (((((((p5 ∧ True) ∨ (p1 ∧ (p5 → False))) → p4) ∧ (p5 ∧ p4)) ∧ p5) ∨ p4) → False)) → (p4 → (p4 ∧ (p1 ∧ p1)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : ((((((p5 ∧ True) ∨ (p1 ∧ (p5 → False))) → p4) ∧ (p5 ∧ p4)) ∧ p5) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((((((p5 ∧ True) ∨ (p1 ∧ (p5 → False))) → p4) ∧ (p5 ∧ p4)) ∧ p5) ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h12 := h10 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69962106602624366137326464400 : ((((((((p2 ∨ True) ∧ (False ∨ p4)) ∨ ((False ∧ (((p2 ∨ p1) ∨ p5) ∧ p4)) ∨ (p3 ∨ (p2 ∨ p1)))) ∨ True) ∧ True) → False) ∧ p3) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p2 ∨ True) ∧ (False ∨ p4)) ∨ ((False ∧ (((p2 ∨ p1) ∨ p5) ∧ p4)) ∨ (p3 ∨ (p2 ∨ p1)))) ∨ True) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656707477193005322039861789821 : (((((p4 ∨ ((False ∨ (p4 ∨ p3)) ∨ p3)) ∧ ((p1 → ((p3 ∨ ((False ∧ p1) ∧ p5)) ∨ ((p5 ∧ False) ∧ p4))) ∨ False)) ∨ (p5 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171368681353530709179863138768 : (((((True ∧ (((p2 ∨ False) ∧ p1) ∨ (p4 ∨ p2))) ∧ p1) → (p4 ∧ p5)) ∧ p4) ∨ (((p4 ∨ p2) ∨ (False → p5)) ∨ ((False ∨ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9113728356055864366750054375 : (((((((p4 ∨ p3) → p1) → ((p5 → p1) → False)) ∨ (p4 → True)) ∨ (False ∧ (((p5 ∨ ((p2 ∨ p1) → False)) → True) ∨ p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653433275434114808849846771211 : ((((p4 → ((False ∨ ((p1 ∨ p1) → (p4 → ((p1 → True) → (p2 ∨ (p2 ∧ ((p5 ∧ p3) ∧ False))))))) ∨ (p5 ∨ True))) ∧ (True ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112584466365223689179365724051 : (((((True → (p4 ∧ (p3 ∧ (((True ∨ p2) → ((p5 ∨ p2) ∨ ((p4 ∨ p3) → True))) → True)))) ∨ p3) ∧ (p4 → True)) → p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56538142665785886843816428820 : (((p1 ∨ ((True ∨ True) ∨ p2)) → ((p4 ∧ True) → (p2 → (((True ∨ ((((p5 ∨ p5) ∨ (True ∨ p1)) ∨ False) ∧ p2)) → p5) ∨ p2)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321553804311621463595858672432 : (p4 ∨ (p2 → ((True → (p4 ∨ (((p3 ∧ (p3 ∨ p1)) ∨ p3) → ((p2 → p3) → (False ∨ (p4 ∧ p4)))))) ∨ ((True → p4) ∨ (p4 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164747680163149468971554709036 : ((((p3 → ((p3 → (p4 ∧ (p2 ∨ (p1 ∧ (p4 → p3))))) ∧ p1)) ∨ (p1 → p2)) ∨ p5) ∨ (((p2 → ((p4 → True) ∨ False)) ∨ False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724633997517183285753212912424 : ((((p1 ∨ (p5 → p2)) ∧ (False ∨ ((p5 ∨ (((p5 ∧ True) → (True ∧ (p2 ∨ ((True ∨ p2) ∧ (True ∧ (p4 → p1)))))) → p4)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178462668072279828849367970032 : (((p4 ∨ ((False ∨ p1) ∨ ((True ∧ p2) ∧ p5))) ∧ ((p3 → p5) → p5)) ∨ ((((p4 ∧ p3) ∧ p5) ∧ (p5 → p1)) ∨ ((True ∨ p1) ∧ True))) := by
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
theorem thm_5_vars_140404893982669740595201780236 : (((((p1 ∧ p1) ∨ (True → ((((True ∨ p2) → p2) → ((True → True) ∧ p5)) → p2))) ∧ p4) → (p2 → (False → False))) → ((p5 ∨ True) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689905357285125818324219863082 : (((((p1 ∨ p3) → ((p1 ∨ (p4 ∧ p4)) → ((p1 → p3) → ((p2 ∧ False) ∨ p3)))) ∨ (((p5 → (p1 ∧ (p5 ∧ p1))) ∨ p1) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42268669633762535751645673666 : (((p1 ∧ (((p4 ∧ False) → (p5 ∧ ((p2 → (p3 ∧ p1)) ∨ (True ∧ True)))) → ((False → (False → p3)) ∧ (p3 ∨ (False ∧ p3))))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678181643696810087786354648966 : (((((p3 → (((((True ∧ p1) ∨ False) ∨ p3) ∧ (p4 ∨ p3)) ∨ False)) → ((p4 ∧ (p3 ∧ True)) ∨ False)) ∨ ((p3 → p3) ∧ (p5 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254168283930431885804723385121 : ((p2 ∧ p1) → ((p4 ∨ (((p5 ∨ ((p2 ∧ p3) → p1)) → (p5 ∨ (p4 ∧ (p5 ∨ True)))) ∨ p3)) ∨ (p2 ∧ (((p4 ∨ p2) → False) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807636210923502606879151534161 : (((p4 → (((p3 ∨ False) → (p4 → p3)) → (p4 ∧ (p1 → ((((False → True) ∨ p1) → p2) ∨ ((False → False) → (p2 → (False → p5)))))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57163427222963834748623846394 : ((((p2 ∧ False) ∨ p3) ∨ (((p3 ∨ ((p5 ∧ ((p4 ∧ p5) → True)) ∧ True)) → ((p2 → p1) → (p1 ∨ p3))) ∨ ((p2 ∧ p2) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809795599624224533087074717088 : (((p5 → (((True ∧ p5) → ((((p1 ∧ p4) ∧ (p1 ∨ (p2 ∨ p5))) ∧ (p1 ∨ (p5 ∨ ((True ∨ p4) ∧ p4)))) ∨ True)) ∨ (p5 ∨ True))) ∨ p2) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179247204208311912350063284521 : ((p5 ∧ ((p2 ∨ (p3 ∧ ((True ∨ False) ∧ True))) → ((False → p1) ∧ False))) ∨ (((True ∧ (p2 ∨ (False → p3))) ∧ False) ∨ (p5 ∨ (True → True)))) := by
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
theorem thm_5_vars_199601330503989100155699724798 : (((((False → p5) ∨ (True → p1)) → False) → False) → (((p4 → ((True ∨ p2) ∧ p5)) ∧ p2) ∨ ((False ∨ (p4 → ((p4 ∨ p5) ∨ p5))) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115957189269934403977288777968 : (((p2 → (False ∨ (False ∧ p4))) ∨ (p3 ∧ (((((False → p2) → p1) ∧ ((p2 → False) → p5)) ∨ p4) ∧ ((False ∧ False) ∨ True)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166018836078822643050853322870 : (((p4 ∨ False) ∨ (((p2 ∨ ((p2 ∧ p3) ∧ p1)) ∨ (p3 ∧ p3)) ∨ (False ∨ (p1 ∨ p2)))) ∨ ((False ∧ ((p2 ∧ (p2 → False)) ∨ p3)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196840509874388515814872290835 : (((p5 ∧ (((True ∧ p2) ∨ p2) ∨ p5)) ∧ p4) ∨ ((p1 ∨ ((p5 → True) ∨ p4)) ∧ (p2 → ((((p2 ∨ False) ∨ (p3 → p5)) ∧ p5) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65927100220032668586322812039 : ((p4 ∨ (p5 ∧ (p5 ∨ ((((p5 ∧ True) ∨ (True ∨ ((p3 ∨ p1) ∧ p1))) → (p1 ∨ p3)) ∧ ((p3 ∨ True) ∨ (p2 ∨ (True ∧ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301390922101641739168002145920 : (False ∨ ((p4 ∧ (p1 → (True ∨ False))) ∨ ((((((p5 ∨ True) ∨ p2) → p2) ∨ ((False ∧ p1) ∨ p3)) ∧ p4) ∨ ((False → (p2 ∨ p3)) ∨ p2)))) := by
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
theorem thm_5_vars_134768352244025715577739062107 : (((True ∧ ((p4 ∨ (((((p5 → p4) ∧ p1) ∧ False) → (p4 ∨ (p5 ∧ (p5 ∨ (p5 → p5))))) ∧ p4)) ∧ p5)) → False) ∨ ((True ∧ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137821133842978538975098768941 : ((p3 ∨ ((((p4 ∨ p3) ∨ ((True → (p5 ∨ (p3 → ((True ∧ (p4 ∧ True)) ∨ (p1 ∨ True))))) ∨ p3)) ∧ True) → p3)) ∨ (p3 → (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205501580160963674460928044633 : (((p3 ∧ False) ∧ (False ∨ (p5 ∧ p5))) ∨ (((False ∨ (((True ∨ (p1 ∧ (p5 → p1))) ∧ p2) ∧ p1)) → ((p3 ∨ p4) ∨ True)) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774666161932237436090603809792 : (((False ∨ ((((False ∨ ((p4 → p3) → p2)) ∨ p5) ∧ (True ∨ p3)) → ((p1 ∧ p5) ∧ ((((p5 ∧ (p4 → p3)) ∨ p3) → p2) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314263704921104801404711342131 : (p3 ∨ (((False ∨ p4) ∧ (p1 ∨ ((p2 → False) ∨ ((p2 ∨ p4) → ((p2 ∨ (((p1 → True) → p2) ∨ p2)) ∧ p3))))) ∨ (False → (p5 → True)))) := by
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
theorem thm_5_vars_112423587775983902164292332242 : ((((p3 → (((p5 → True) ∧ (False ∨ ((p1 ∨ False) ∨ p3))) ∧ (p1 → (p1 ∧ ((p5 ∧ (False ∨ p2)) → p5))))) ∧ p3) → p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647557076901072098657730136555 : ((((p5 → (((((True ∨ ((p2 ∧ ((p2 ∧ p4) ∨ p5)) ∨ (True ∧ (p3 ∧ True)))) ∧ (p2 ∨ (p2 ∨ p2))) → p5) → p4) → p1)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77504820396303477127374630849 : ((((p5 → False) → ((((True ∨ (p1 ∧ ((p3 ∧ (True → p2)) ∧ p1))) → ((p4 ∧ ((p5 → p3) ∨ p4)) ∨ p3)) ∧ p1) ∨ True)) → p5) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → False) → ((((True ∨ (p1 ∧ ((p3 ∧ (True → p2)) ∧ p1))) → ((p4 ∧ ((p5 → p3) ∨ p4)) ∨ p3)) ∧ p1) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797307282280019819769440620109 : (((p1 → ((((p5 → (p1 ∧ False)) → (((p3 ∨ p1) → (((p1 ∧ True) ∨ (p2 ∨ False)) ∨ (p3 ∧ p3))) ∧ p2)) → (p1 ∧ False)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_305194598382518534182972055647 : (p1 ∨ ((p3 ∨ (p4 ∧ (((p5 ∧ True) ∨ (((False ∨ (p2 ∧ (p2 ∨ p4))) ∨ p2) → (p5 ∧ p1))) ∧ p5))) ∨ ((p4 → (p1 → p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644571328146141496591037206807 : ((((p1 ∨ ((True ∧ ((False → p1) ∨ (p2 ∨ ((p1 ∧ False) ∧ (((p2 → (p3 → p3)) → p2) → p1))))) ∧ (True → (p4 → p4)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317731494561021258941698943014 : (p4 ∨ (((((True ∨ ((p2 → True) ∨ (((p4 ∨ (False ∨ p4)) → p1) ∧ (p5 ∧ True)))) → (p4 ∧ p1)) ∨ p3) ∨ (p5 → (False ∨ p5))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303241962899895107840197776787 : (False ∨ (p5 → (((((p5 ∨ ((True ∧ p1) ∨ p4)) ∨ p2) ∧ (((True ∨ p2) → p3) ∧ (p1 ∨ p1))) ∧ (p1 ∨ p3)) → ((True ∧ False) ∨ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Conjunctions on the left can always be decomposed.
        let h21 := h6.left
        let h22 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h23
        case inr h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h26
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h6.left
        let h31 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h32
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h4
          case inl h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h36
          case inr h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h35
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h6.left
    let h40 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h42
      case inr h43 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h41
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h45 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h45
      case inr h46 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h44



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7661729709183453449607822775 : (((((((((False ∧ p5) → p4) ∧ p1) → ((p5 ∨ ((p1 ∨ p3) ∧ p5)) → ((True → (True ∧ True)) ∧ False))) ∧ True) ∧ p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158631863623378869015848497858 : ((p1 ∧ ((p1 → ((p1 ∧ ((p4 → p5) ∨ (p1 → ((p4 ∧ (True ∨ p3)) → p2)))) → False)) ∧ True)) ∨ ((p3 → (p2 ∨ (p4 → p4))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164113707337450293666805802576 : ((p2 ∨ (p1 → (((((p3 → True) ∨ ((p2 ∧ p4) ∧ (p2 ∨ p3))) ∨ p3) ∨ False) ∧ True))) ∧ ((p4 ∨ (p5 ∨ (False ∧ p3))) ∨ (p5 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712271214536327726652632812685 : ((((((False ∨ False) → (p5 ∨ True)) → False) ∨ ((((True ∨ p2) → (True ∧ p4)) ∨ ((((p3 ∧ p4) ∧ (p2 ∧ p5)) ∨ p4) → True)) ∨ p3)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114007126493847528443367845896 : (((((True ∧ ((False ∧ (p4 ∨ False)) ∨ p2)) ∧ (((True → ((True ∧ p2) ∨ p2)) → False) → p3)) ∧ p5) ∨ (p3 ∧ (p1 ∧ True))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50492363405032898827957330432 : (((p5 → ((((True ∧ p2) ∧ (p1 ∨ (p3 ∧ (p2 ∨ p2)))) ∨ (False → ((p1 → p1) ∨ p3))) → False)) ∨ (p5 ∨ ((p4 ∨ p3) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61773291901126141384876979655 : ((p2 ∧ ((((p2 → ((((p4 → False) ∨ p2) ∨ ((p1 ∧ p2) ∧ p1)) ∧ p3)) ∨ p5) → ((((p1 ∨ True) → p5) ∨ p1) ∨ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321578954939078101190637243605 : (p4 ∨ (p2 → (False ∨ ((((True ∧ (((((p2 → p5) ∨ p5) ∨ (p2 → p4)) ∨ p5) → p2)) ∧ False) → True) → (((p1 → p5) ∨ True) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111612536484258327634259542356 : (((((p3 ∧ (p4 ∨ (p5 ∧ ((p3 → p3) ∨ (((p5 ∧ (p5 ∧ (p2 → (p3 ∨ p3)))) → p1) → False))))) ∨ p1) ∨ False) ∨ p3) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226595035107940138344710318068 : (((p5 → False) ∨ p5) ∨ (((((((p5 ∨ True) ∧ True) → ((p5 ∧ (p4 ∨ p3)) → p5)) ∧ p5) → ((False → True) ∧ p4)) → (p4 ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50692305727663575486768170634 : (((((True → False) ∧ p5) ∨ ((((p1 ∨ (p2 ∨ (p2 → p4))) → p5) ∨ False) ∨ (p3 → (p5 ∧ p4)))) → (p4 ∧ ((p3 → p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171685255668992936264320489620 : (((p3 ∨ (p4 → (((((p2 ∧ False) → False) ∧ p2) → (False ∧ p1)) ∨ p3))) ∨ p5) ∨ ((True ∨ ((p5 ∧ p4) ∨ p2)) ∨ (p5 → (p3 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231769555256021201223317753303 : (((p3 ∧ p4) → True) → ((p4 ∨ p1) ∨ ((p3 ∧ ((p4 ∨ ((False ∧ ((((p4 → p3) → True) ∧ p3) ∨ False)) → p3)) ∧ p4)) ∨ (p2 ∨ True)))) := by
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
theorem thm_5_vars_167282315536543961278691757902 : (((((True ∨ (p1 → (p5 → (True ∨ True)))) ∧ (((True ∨ True) ∨ p3) ∧ p5)) ∨ p1) → False) → (((False ∧ p5) ∨ False) ∨ (p3 ∨ (p1 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((True ∨ (p1 → (p5 → (True ∨ True)))) ∧ (((True ∨ True) ∨ p3) ∧ p5)) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149812696836740799969569639562 : ((p1 ∨ (((p5 ∧ ((True → p5) ∧ ((((p3 ∧ (p2 → p4)) ∨ (True ∨ p4)) ∨ p1) → p3))) ∨ p3) ∧ p3)) ∨ ((p1 ∧ (False → p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66583315167766471175488628087 : ((True → ((((((p5 ∨ ((p5 ∨ (False → p5)) ∨ ((p4 → p4) → p4))) → p4) ∧ (p4 ∨ True)) ∨ False) ∨ p1) ∧ ((p5 ∨ p5) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207780884610961798190318240431 : (((p5 ∨ ((p2 → True) ∧ False)) → True) → (((((p2 ∨ p1) ∨ (p3 → p5)) ∧ True) ∨ (((p3 → p4) ∧ p1) ∧ False)) ∨ (True ∧ (p3 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782462291734379388884017854133 : (((p3 ∨ (((p5 → ((p4 → ((p3 ∨ ((p3 ∨ p1) ∨ p5)) ∨ p1)) ∨ p2)) ∧ (p4 → ((False → p3) ∧ (p5 → (p3 ∧ p1))))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191267349214265680962955094999 : (((True ∨ p4) ∧ (p5 ∨ (((p1 ∨ p3) ∧ p1) ∧ p5))) ∨ ((p2 ∧ p3) → (p3 ∨ (((p3 → ((p1 ∨ p3) ∨ p1)) ∧ p2) ∧ (False → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752887773965703247346092045470 : (((False ∧ (((((p5 → p1) ∧ (p4 → ((True → (p1 ∨ (p2 ∧ p4))) ∧ p1))) ∨ (((False → p4) ∧ p2) ∨ (p1 → p5))) ∨ p5) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44151525439613238349584172914 : (((((((((p5 → (((p3 → p3) ∨ p1) ∨ (p5 ∧ p2))) ∧ p2) ∧ False) ∨ (p2 → p3)) ∨ p4) → p2) → ((p5 ∧ True) → False)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380991555823507375462103658522 : (((((True ∧ ((p3 → True) ∧ ((((False ∨ p4) ∨ p3) ∨ ((p5 ∧ p1) → p2)) → ((p2 → p3) ∨ ((p2 ∧ p1) → True))))) ∧ p2) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_720705209077715438291574574652 : ((((((False → p4) → p2) → p4) → ((p3 ∧ (p2 ∧ p1)) → ((p3 → (False ∧ (p5 ∧ (False ∨ True)))) ∨ (((False ∧ p2) ∧ p3) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156907136553398617338040712267 : ((((((p1 → (((p1 → (p4 ∨ p5)) ∨ p5) ∨ p3)) ∨ ((p1 ∨ p1) ∧ p2)) ∨ True) → False) ∨ p3) ∨ (p3 ∨ ((p3 → (p3 → p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56965371667318858107019172769 : (((p3 ∨ (p1 ∧ False)) ∧ (p2 ∧ ((False ∧ (((p5 → (p2 → p3)) ∨ False) → (p1 → ((p5 ∨ (p5 → p5)) → False)))) ∨ (p3 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141385797701164462675679647510 : (((((p1 ∨ True) ∨ p3) → p1) → ((p3 ∨ (p1 ∧ p3)) ∧ ((p1 → (p5 ∧ p5)) ∧ (p4 → (True ∨ (p2 → p1)))))) → (p5 ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160841652581995799586243480292 : (((((p1 ∨ p4) → p3) ∧ p1) ∧ ((False ∧ ((p2 → p4) → (p3 ∧ ((p4 ∨ p1) → p3)))) → p2)) → ((((p5 ∨ p2) → p5) → p2) ∨ p1)) := by
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
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219647559162809841271882986025 : ((False → (True ∧ (p1 ∧ p3))) → (((p3 ∨ p3) → ((False ∨ False) ∧ (p4 → (p2 ∨ ((p5 → p2) → True))))) ∨ ((False ∨ p2) ∨ (p4 ∨ True)))) := by
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
theorem thm_5_vars_161568286817448527040086119582 : ((True ∨ ((((True ∧ p4) → p5) ∨ (p1 ∨ ((p1 ∧ p2) → ((False → p5) ∨ (p1 → p3))))) ∨ p5)) → ((False ∨ (p3 ∨ p2)) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744802329640424589009554141224 : ((((p3 ∧ p3) → (((p5 ∧ ((p1 → (p4 ∨ p1)) → (p2 → p5))) ∧ (p4 → (p5 → ((p1 ∨ (p2 ∧ (p2 ∨ p5))) → p3)))) ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_114615031679721477183510161614 : (((p2 → (p1 ∧ ((((p3 ∨ p3) ∨ p5) ∧ ((p5 → True) ∧ (p5 ∨ p5))) ∧ p1))) ∧ (p5 ∨ ((p5 → (True → p2)) ∨ p5))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735926554236799174535245030547 : ((((True → p1) ∧ ((p5 ∧ False) ∧ ((p5 → p1) → (((p4 → False) ∧ p4) ∧ ((((True → (p2 ∨ (p1 ∨ p3))) ∨ p1) → p4) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65718572970508852526515341280 : ((p4 ∨ ((False ∧ (p3 ∨ ((p4 ∨ ((((p5 → p1) → p3) → ((p5 ∨ p2) ∨ p1)) ∧ p3)) ∨ ((p5 ∨ p2) ∧ False)))) ∨ (True → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111758866308896430838874156329 : (((((((((((p1 ∨ True) ∨ (p1 ∨ p3)) ∨ p5) → p1) ∧ p1) → p3) ∨ (False ∧ (p3 ∨ False))) → p2) ∧ (True ∨ p4)) ∨ p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56668687765714220164839957954 : ((((False → p2) ∧ p5) ∧ ((p5 ∨ False) ∧ (((True ∧ p2) → p3) ∧ ((p2 ∨ (p1 ∨ ((p1 ∧ p3) ∧ p4))) ∨ ((p1 → False) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670833890472886819144388608581 : ((((p2 ∧ ((p1 → (True → (((p3 ∨ (False → (True ∧ (p2 ∨ p4)))) ∧ (p2 ∨ (True ∧ False))) → False))) ∧ p3)) ∨ ((p4 → p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206127280888392544984909145222 : ((p4 ∧ ((True ∨ p4) → (p1 ∨ p1))) ∨ (((p5 → (True ∨ (p1 → p3))) ∧ ((p2 ∧ False) → (p4 ∨ (True ∧ (p4 → (True ∧ True)))))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354775544800624704143610032732 : (p5 → (((p4 ∧ (False ∨ ((True → (True ∨ (p1 → p4))) ∨ p1))) ∨ (((True ∧ ((False ∨ True) ∧ p4)) → ((p5 ∨ p4) ∨ p2)) → False)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63202891234609575387302275730 : ((p5 ∧ (((p1 ∧ ((True ∧ p2) ∨ True)) ∧ ((p3 ∨ True) → (p3 ∧ ((False ∨ (True ∨ p3)) ∧ p1)))) ∧ ((p2 → True) ∨ (p2 → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299269726546612899373692085259 : (False ∨ ((((p2 ∨ (p1 ∨ (p4 ∧ (p3 → p1)))) ∨ ((p5 ∨ (p2 → (p5 → p2))) ∨ p1)) ∨ (p1 → (p1 ∧ (p1 → (p1 ∨ p3))))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199488535933436787094399380476 : (((p5 ∨ (((p3 ∧ p5) ∧ False) → True)) ∨ p1) → ((p1 → (((((p5 → (p1 ∨ p4)) ∧ False) ∨ (False ∨ p1)) → False) ∨ True)) ∨ (p1 ∨ p3))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619651049718954101666965103418 : (((((p3 ∧ p1) ∧ ((p4 ∧ ((p4 → ((False ∧ p3) ∨ ((p3 ∧ p1) → p1))) ∧ p3)) ∧ ((False → (False ∨ (False ∨ p5))) ∨ p1))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147305342940079168917612909442 : (((((p1 ∨ ((p4 ∧ ((p1 ∨ p3) ∨ False)) → p5)) ∨ (False → ((p3 ∨ (p3 ∨ p5)) ∨ p3))) → False) ∨ True) ∨ ((p2 → p4) ∨ (p4 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325723160814478129137183866694 : (p5 ∨ (p1 ∨ (p2 → (((((p5 → p5) ∧ (p2 ∧ ((p5 ∨ p4) → False))) ∧ p2) ∧ (p1 → (False ∨ (((True → p3) ∧ p2) ∧ p4)))) ∨ p2)))) := by
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
theorem thm_5_vars_165654669646849451069902170868 : ((((p4 ∨ ((p4 ∧ p4) ∨ False)) → p1) ∨ ((p5 ∨ (p3 ∧ p4)) ∨ ((False ∨ p4) ∨ p4))) ∨ ((p3 → (((True ∧ p2) ∨ p5) ∨ True)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316630149187670563529876848681 : (p3 ∨ (p4 ∨ ((p4 ∧ (((((p5 → p4) ∨ p3) → p1) → ((p1 → p4) ∨ p3)) ∧ p4)) ∨ (p4 → ((((True → p2) ∧ p5) ∧ p4) → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51166429979361354014671489308 : ((((p1 ∨ (p3 → ((p3 ∧ (True ∧ (p1 ∨ (p4 → (False ∧ p2))))) ∨ p5))) ∧ (p4 ∨ p4)) ∨ (p5 ∨ (p2 ∧ ((True ∧ p5) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684986383855366652156443044349 : ((((p4 ∧ ((p1 ∧ ((p3 ∧ p1) → ((p4 ∧ (p3 ∧ p4)) ∧ (True ∧ (p1 ∨ p3))))) ∨ False)) ∨ (((p5 ∧ False) ∧ True) → (p5 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65722585251386028453150014191 : ((p4 ∨ ((((((p3 → (p2 → ((p5 ∧ p1) ∧ (True ∧ p1)))) → (False ∨ p5)) ∧ (p3 ∧ (p5 → True))) ∨ True) ∨ p2) → (p1 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116718130311844769939461965129 : (((p2 ∧ p1) ∨ (p2 → ((((p5 → (p1 ∧ p1)) ∨ (p2 ∧ p4)) ∨ (((p4 ∨ False) → p2) → p2)) ∧ (p2 ∧ (False → p3))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



