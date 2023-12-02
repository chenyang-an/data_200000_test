variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181399068260524564823807409338 : ((p2 ∨ ((((p4 ∨ ((p1 → p1) ∨ False)) ∧ (True ∧ p5)) → p3) ∧ p2)) → (((p4 → p4) → False) → ((p1 → ((p2 ∧ False) ∧ p2)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h9
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h15
    -- False on the left can always be used.
    apply False.elim h17
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h24
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h23
    -- False on the left can always be used.
    apply False.elim h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h29 : (p4 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h31 := h2 h29
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667677142547854528798560509910 : ((((p4 ∧ ((((p2 ∨ ((p1 ∧ p5) ∨ p3)) → (((True → ((p2 ∧ p1) ∧ p3)) → p2) ∧ p4)) ∧ p5) ∧ p2)) ∧ ((False → p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134920957392539448550676960051 : ((((p4 ∧ (p5 ∧ ((p1 ∧ p1) ∧ ((p1 → (False ∨ (p1 ∧ (p4 ∨ (p2 ∧ p3))))) ∨ True)))) ∨ p5) ∧ (p3 ∨ True)) ∨ (True ∨ (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148680097938239232983864752248 : ((((p4 ∨ (p4 ∨ (p5 ∨ False))) ∨ (False ∨ p4)) ∨ ((p3 → (p5 ∨ (p5 → (True ∧ (False → p5))))) ∨ p5)) ∨ ((True ∧ p1) ∧ (p2 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208950137170891289762573258379 : ((True ∨ (((p5 → p5) ∨ p4) ∨ True)) → (((p2 ∨ (((((False ∨ p5) ∨ p4) → p3) ∨ (p2 ∧ p1)) ∨ (p2 ∨ p2))) → p4) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763745735835091535633540563053 : (((p3 ∧ (p1 ∨ ((p4 → (((((False ∧ (False → True)) ∧ ((False → False) → (p3 ∨ p3))) → p4) → p2) ∨ True)) → ((p1 ∨ p4) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53171952563282606690018303032 : ((((((p2 → p1) ∧ (p2 ∧ ((p2 ∨ p1) ∨ p1))) → p1) → p4) ∨ ((p5 ∨ ((p1 → (((False → p4) → False) ∨ p5)) ∨ True)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218609204255517478143662798451 : (((p4 → p4) → (p5 ∨ False)) → (p4 ∨ (((((p5 ∧ p4) ∨ (p1 → p4)) ∧ (p3 → True)) ∨ True) ∨ (p2 ∧ ((p5 ∧ False) ∧ (p3 ∧ False)))))) := by
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
theorem thm_5_vars_349032535865085352782107213965 : (p3 → (p5 ∨ (((p3 → (p4 ∧ (p1 ∨ p1))) ∧ ((p4 → (p3 ∧ False)) → ((False ∧ ((((p1 ∧ True) ∨ False) ∨ p1) → False)) ∨ True))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63110027689227499284066726432 : ((p5 ∧ ((((False → (p4 → (((p3 ∨ p1) ∧ (False → (p1 ∧ (p1 ∨ (p5 ∨ (p5 ∨ (p2 ∧ p3))))))) ∧ p4))) ∨ p2) ∧ p5) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246705034707985529702894148183 : ((p5 ∧ p4) ∨ (((False ∨ (p1 ∨ (p3 ∨ p5))) ∨ True) ∨ (p3 ∨ (((p4 ∨ (((p4 ∧ False) ∨ p1) ∨ p4)) ∨ ((p1 ∧ p1) ∧ p3)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141251437902088248378954577962 : (((True ∨ (p1 ∨ ((p5 → p3) → p1))) → ((p1 ∨ (((p4 ∨ p5) → (p5 ∨ (True ∧ (p5 → p4)))) ∨ p5)) ∧ False)) → ((p4 → p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p1 ∨ ((p5 → p3) → p1))) := by
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
theorem thm_5_vars_345375317422555043368168386981 : (p3 → ((((p1 ∧ (p5 ∧ p5)) ∨ ((((p5 ∨ p2) ∧ False) ∨ p4) ∧ ((p2 → p2) → ((p3 ∧ False) ∧ ((p5 ∧ p2) ∨ p2))))) ∨ False) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171356618646750484391734810688 : (((((p1 → ((p5 → p1) → (p3 ∧ (p5 ∨ p3)))) ∨ p4) ∧ (True ∧ False)) ∧ p3) ∨ (False → (p5 ∨ (p2 ∨ (p5 → (p1 ∨ (p1 → True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654756481461995246080034612030 : (((((((((True → p5) → p3) → (p2 → ((p4 ∧ ((p3 ∧ p4) ∨ True)) ∨ (False → (p1 → p1))))) → p4) → False) → p3) ∨ (True ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801815443140078253002422587337 : (((p2 → ((True ∨ (p5 → p5)) → (p5 → (((True → (((p3 ∧ (p4 ∨ (p4 ∧ p1))) ∧ (p2 ∧ p5)) ∨ p1)) ∧ (True → p3)) ∨ True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157920837043519715032853816224 : (((True → ((p4 → ((False ∨ (p4 → p5)) ∨ p2)) ∧ False)) → ((p4 ∧ ((p2 ∧ p1) → p4)) ∧ False)) ∨ (True → ((p4 → p5) ∨ (p4 → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49116883023908614631876120408 : (((((((False ∧ p5) → (False ∨ ((p2 → False) → (p3 ∨ p3)))) ∧ p3) ∨ p2) → (True ∧ ((p4 → p2) ∧ p3))) ∨ (False ∨ (False → p3))) ∨ p5) := by
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
theorem thm_5_vars_86600728452507790447275378494 : ((((p5 → (True ∧ ((p3 ∨ True) ∨ p2))) → False) ∧ ((((True → (p5 ∧ p5)) ∧ (((p4 ∨ p3) → p4) ∧ p5)) → (p1 → False)) → p4)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (True ∧ ((p3 ∨ True) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197444273305429718506394516043 : (((((p5 → True) ∧ p1) ∨ p1) ∧ (p2 ∨ p3)) ∨ (((p2 ∧ (p1 ∨ True)) ∨ (True ∧ (True → p1))) ∨ (p5 → ((False ∨ p5) ∨ (False ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168068907988596546516578490070 : ((((False → False) ∧ (True ∧ p2)) ∧ (((((p3 ∨ False) → p2) ∨ p4) ∨ p5) ∨ (p3 ∧ True))) → ((p3 → (p1 ∧ ((True ∨ False) ∧ p3))) ∨ True)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
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
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110640230506409207078306935486 : ((p5 → (((((p5 ∧ (p4 ∧ p1)) ∧ p2) → p2) ∨ p4) → (((p3 ∧ p1) ∨ (p4 ∧ ((p2 → p1) ∧ (False ∧ False)))) ∨ True))) ∧ (p4 → p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52381330291500997358132167334 : (((((p5 → ((False ∨ p4) ∨ (False → p3))) → p2) → (p2 ∨ (p4 ∨ True))) ∧ ((p5 ∧ p3) ∧ (p1 ∧ (((True ∨ p2) ∧ p3) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189219847022259805305076132456 : (((p5 ∨ True) ∨ (p1 ∨ ((p1 → p4) ∧ (p5 ∧ p5)))) ∧ (p4 → (False ∨ ((((p4 → p4) → (((p3 ∨ True) ∧ p2) ∧ p3)) ∨ p5) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734640504898128257301714305982 : ((((p1 ∨ p3) ∧ (p4 → (((((((((True ∧ False) → (False ∧ p4)) ∨ p3) ∨ True) ∨ True) → False) → (p5 ∧ p2)) ∧ (p4 → p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726705271014319844749278641368 : (((((p4 ∧ p2) → p1) ∨ (((p3 → p2) ∧ (p5 ∨ ((((p3 ∨ True) ∨ p5) → True) → (p5 ∨ True)))) ∨ ((p1 → (p2 ∧ p4)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57983017119007606036342220818 : (((p4 → (p1 ∨ False)) → (True → (((((p1 → False) ∨ p5) ∧ (((p4 → False) ∧ ((p1 ∨ (p1 ∧ False)) ∨ p3)) ∧ p5)) ∨ True) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_468747568495624207781516271341 : ((((((p3 ∧ ((p3 → p5) → (p2 ∧ (p5 → p5)))) ∨ (p2 ∨ p4)) → p4) → ((False ∨ ((p2 → (p4 ∨ False)) ∨ (p2 ∨ False))) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∧ ((p3 → p5) → (p2 ∧ (p5 → p5)))) ∨ (p2 ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721786701072414902469470149238 : ((((p2 ∨ (True ∧ (p2 ∨ p3))) → ((p1 ∨ ((p2 ∧ p3) → (p5 → p3))) → (p3 ∧ ((((p1 ∨ p3) → (p2 ∨ p1)) ∨ False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201132087906348653493085966707 : ((False → (((p5 ∨ p2) ∧ (p1 ∧ p1)) ∧ False)) → (((p1 ∨ p3) → ((False ∧ (p4 ∧ (((p3 → p4) ∨ p5) → p3))) ∨ (True → True))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179320875352029547226119082176 : ((False ∨ (p5 → (((((p2 ∧ (False ∧ p4)) → p4) → p5) ∧ p3) ∧ p4))) ∨ ((((p5 ∨ p4) → p2) → p1) → (((p1 → p2) ∧ p3) → p3))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183142585006276582867727490245 : ((True ∧ (((p3 ∨ (True ∧ p2)) ∨ ((False ∧ p1) ∨ p4)) ∨ True)) ∧ (True ∧ ((p2 → (p2 ∧ (((p4 → (True → p1)) ∧ p1) → p2))) ∨ False))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181078382958820358965912591120 : (((p3 ∨ p5) → ((False ∨ (p4 → ((False ∧ p1) ∨ (p4 ∧ p2)))) ∧ p2)) → (p4 → (p2 ∨ (((((p3 ∧ p5) → p4) → p4) → p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609926377964872760671875948750 : (((((p4 → (((((True ∨ (p3 ∨ p4)) → (((True ∨ (False ∧ p5)) → (p3 ∨ True)) → (p1 → p5))) → p5) ∨ False) → p5)) ∨ p1) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_137044721474502607940516392751 : (((False → False) → (((False → p1) → (p2 ∧ (p2 ∧ (False → (False → (p5 ∨ (True ∧ p4))))))) ∧ ((p4 → False) → p2))) ∨ (False → (p5 ∧ False))) := by
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
theorem thm_5_vars_624877204326065088313376676810 : ((((p5 ∨ (((p3 ∨ True) → ((p4 ∨ p3) ∧ ((True ∧ True) → p5))) ∧ (((p3 ∨ (p5 → (p3 ∧ False))) ∨ False) ∨ (True → p4)))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313942025911931307446041904369 : (p3 ∨ ((((((((p4 ∨ p1) ∨ p3) ∨ ((p4 ∧ (True → p1)) → True)) ∧ (p3 ∨ p5)) ∧ ((True ∧ p1) ∨ p1)) ∨ False) → p3) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174587192794097185292403995387 : ((((p5 ∨ (True ∨ p1)) ∨ p2) ∨ ((p4 → p1) ∨ (p3 ∧ ((True → p5) ∨ p5)))) → (True ∧ (((True → (p1 ∨ p2)) ∨ p5) ∨ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h7
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- False on the left can always be used.
          apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51414556332984418225927886223 : ((((True ∧ ((False ∧ (p2 ∨ ((p5 ∧ False) → False))) ∨ (True ∨ (p2 ∧ (p4 ∧ p1))))) → p1) → ((((p1 ∨ p5) ∧ p4) ∨ p1) ∨ p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ ((False ∧ (p2 ∨ ((p5 ∧ False) → False))) ∨ (True ∨ (p2 ∧ (p4 ∧ p1))))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799417820460684988838448968403 : (((p1 → (False ∨ (((p3 ∨ (((p1 ∧ False) ∧ (p1 → (p4 → p3))) ∨ p1)) ∧ p3) ∧ (((False → True) ∨ (False ∧ False)) ∧ (p4 → False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115154674644095866370882100487 : (((False → (True ∨ ((p1 ∨ p3) ∧ (False ∧ ((p5 ∨ True) → True))))) → (False ∧ (p4 ∨ (False ∨ ((p4 ∨ p4) ∧ (p3 ∧ p1)))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64057302663997243265659922494 : ((False ∨ (((p2 ∨ (((p2 ∨ False) → p5) → (False ∧ True))) ∨ (((p1 → False) → p1) → (p1 ∨ True))) ∨ (p4 ∧ (p3 ∨ (p4 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46825007404501604057842789360 : ((((((p1 → False) ∧ ((((p3 ∧ p2) ∧ (p4 → p2)) ∨ ((p3 ∨ True) ∧ p3)) ∧ (p1 ∧ p5))) ∨ (p1 ∧ p1)) ∧ p1) ∨ (True → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643744945248159423124972527487 : ((((p5 ∧ ((p3 ∧ ((p5 ∨ (((p5 ∨ p3) ∧ p4) ∧ (p5 ∨ (True ∧ p2)))) → (p5 ∧ (True → p4)))) ∧ (p2 ∨ (p4 → p5)))) → p4) ∨ p5) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (p5 ∨ (((p5 ∨ p3) ∧ p4) ∧ (p5 ∨ (True ∧ p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h15 : (p5 ∨ (((p5 ∨ p3) ∧ p4) ∧ (p5 ∨ (True ∧ p2)))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h16 := h7 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68202199574192747180374542285 : ((p3 → ((p3 ∧ (p5 ∨ ((p1 ∨ ((p2 ∧ ((p2 ∨ p5) → (p4 → False))) ∧ (False ∨ ((True ∧ p5) ∧ (p2 ∧ p2))))) ∧ p1))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657715669326941624356617707607 : (((((p4 → p1) → ((((p3 → ((True → (p5 ∧ p3)) → (((p5 → p4) → p4) ∨ (False ∧ p1)))) → p4) ∧ p5) ∨ p3)) ∨ (p5 → True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_622016563130846188322515238559 : ((((p2 ∧ (((((True ∨ (p5 ∨ ((True ∧ p1) → (((p2 ∧ p5) ∨ p3) ∧ p3)))) ∨ ((p4 → p4) ∧ p2)) ∧ p3) → False) ∨ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_308627136938330727920885039425 : (p2 ∨ (((True ∨ p2) → ((p3 → ((p4 ∧ (p2 ∧ False)) ∨ (p4 ∧ ((p4 ∨ p4) → ((True → p2) → True))))) ∧ (False → (p1 ∧ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147932961963211262438958226055 : ((((p2 ∨ ((p1 ∨ p3) ∨ p1)) ∧ (p3 ∨ (((True ∧ ((p1 ∧ p1) → p5)) → p1) ∧ True))) ∧ (p3 → p5)) ∨ (((False ∨ True) ∨ False) ∨ p3)) := by
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
theorem thm_5_vars_198254731281393654425301504354 : ((False ∧ (((p2 → True) → (False ∧ p3)) ∧ p1)) ∨ (p2 ∨ ((True ∧ (False ∧ True)) → ((p2 ∨ (p2 ∧ (p4 ∨ ((p3 ∧ p2) → False)))) ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158374190794243338420844927203 : (((p5 ∨ False) ∧ ((False ∧ (p3 ∧ ((True ∧ p3) → False))) ∨ (p5 → (p2 → ((True → p5) → p3))))) ∨ (((p2 ∨ p1) → p1) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55716964416169019956280894193 : ((((p5 → (False ∨ p2)) ∨ p1) ∧ ((p3 → ((True → p5) ∨ ((p5 → False) ∨ ((False ∨ p2) → (p2 ∧ p1))))) ∧ (True ∨ (p4 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35822648584771060975236590820 : ((p3 → (((((False ∨ p3) → p4) ∨ ((p4 → ((p5 ∧ (True ∨ p4)) → (((p2 ∧ p1) → False) → False))) ∨ p1)) ∨ (True ∨ True)) ∨ False)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_307891720637321600958545958142 : (p1 ∨ (p5 → (False ∨ ((False ∨ ((False ∨ (p1 ∨ p5)) ∨ (p4 ∧ (p1 ∧ ((p3 → ((False → p3) ∨ (p5 → (p2 ∨ p2)))) ∧ p1))))) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62698471883799013903792039238 : ((p4 ∧ (((((True ∧ (((False → p2) ∧ p4) ∧ (p2 ∧ p1))) → (((p4 ∧ p1) ∨ p4) → p3)) ∨ p5) ∧ (p5 → (p2 → p3))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117650237403969541468146834808 : ((p3 ∧ ((((p3 ∧ ((p3 → p2) → (False ∧ p5))) ∨ p4) ∧ (((p3 ∧ (p2 → p1)) ∨ p1) ∧ (p5 → p2))) ∧ (p3 ∧ True))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723552156588907068985247304899 : (((((False ∨ p5) → True) ∧ (((False ∨ p3) ∧ (False ∧ ((False ∨ p1) ∧ (True ∧ p4)))) ∨ (p2 → ((p2 ∧ True) → (False ∨ (False → p4)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253990548522571249623842856547 : ((p1 ∧ p5) → ((p3 ∨ ((p4 ∨ p2) ∨ (True ∨ (p5 → (p3 ∨ p2))))) → ((True ∧ ((p4 → p1) → ((p4 → False) ∨ p5))) ∧ (True ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h1.left
        let h11 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h1.left
        let h14 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h1.left
        let h21 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h1.left
        let h29 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h1.left
        let h36 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h1.left
        let h39 := h1.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750658615694467748705348947175 : (((True ∧ (((p4 → (((True → p2) → ((p4 → (p5 ∨ p3)) ∨ (p5 ∧ p3))) → p4)) ∧ True) → (((True ∧ p3) ∨ (p3 ∧ p2)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134262999620207492986006999973 : (((((p3 ∧ p1) → p1) → (((p3 → (((p5 ∧ p5) → p5) ∨ (p1 ∧ (True ∨ p1)))) ∨ (True ∧ p5)) → p1)) ∨ True) ∨ ((p4 ∧ False) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185092293777773269910205302266 : (((p4 ∨ p3) ∨ (p5 ∨ ((((p2 ∨ p3) ∨ p4) ∨ p2) ∨ False))) ∨ ((((p1 ∨ p5) ∨ (p2 ∧ (True ∨ ((p2 → p2) ∧ p5)))) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7921861542512404391524079810 : ((((p2 → ((p3 → ((((p5 ∧ (p4 → (((p1 ∧ True) → p2) → True))) ∨ (p3 ∧ False)) ∧ (p5 ∧ p5)) ∧ p2)) ∨ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204706241651757712737874660824 : (((p5 ∨ ((False ∨ p3) ∧ p1)) ∨ p1) ∨ (((p2 ∨ p4) ∨ p2) → (p4 → ((((p3 ∨ p4) → ((p1 → p1) ∨ p3)) → False) → (p4 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : ((p3 ∨ p4) → ((p1 → p1) ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h10
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : ((p3 ∨ p4) → ((p1 → p1) ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h21
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h17
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h24 : ((p3 ∨ p4) → ((p1 → p1) ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h28
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h29 := h3 h24
    -- False on the left can always be used.
    apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264301111980695220561364453515 : (True ∧ (((p3 ∧ ((p2 ∧ p1) → p4)) → p1) → (((True → (p5 ∧ (p2 → True))) ∨ (p4 → (True → p3))) ∨ ((False → p3) ∨ (p4 ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149611983110652064986044696126 : ((p3 ∧ (True ∧ (((p5 → (True ∨ (p1 → (p3 ∧ p2)))) ∨ (p1 → p5)) → (((True ∨ p3) → False) → p3)))) ∨ ((False → p3) ∨ (p1 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641609017069006368869808259792 : (((((p5 ∧ False) → ((p2 ∨ (((p1 ∧ p5) → (((p1 → True) ∧ ((p2 ∧ True) ∨ p3)) ∧ p4)) ∧ True)) → ((p3 ∨ p2) → p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630205353994860516874396229506 : ((((((p3 → False) ∨ ((False → p1) ∨ ((((p1 ∨ (p2 ∧ p1)) ∨ p3) ∧ p5) → ((False ∧ (p5 ∧ (p3 ∧ p2))) → True)))) ∨ p3) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_676582139628962704834866580649 : ((((p1 ∧ (p2 → ((p3 → (p3 → (((p1 → p1) ∨ ((p5 → p4) ∧ p4)) → (p5 ∨ p3)))) ∧ p3))) ∧ (p4 ∧ (p1 → (False ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117662722375366205784609292090 : ((p3 ∧ ((((p5 → True) → p4) → (((p4 ∨ ((p2 → (p4 ∧ False)) ∧ False)) ∧ p2) ∨ (p4 → p4))) → (p3 ∨ (p1 ∨ p2)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134610573643653917098440722025 : ((((False → (((p4 → p2) ∨ ((True ∧ ((p3 ∨ True) → p2)) ∧ (p1 ∨ False))) ∨ p4)) ∧ ((p1 ∨ p4) → False)) → False) ∨ (False → (p4 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631120845743295307186731460649 : ((((((p2 ∧ (((p3 → True) ∨ p5) ∨ ((p5 → ((p4 ∨ p5) → (True ∨ (p4 → ((True → False) → p3))))) ∨ p1))) ∨ p3) → p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321185630817344894255487704395 : (p4 ∨ (p3 ∨ ((((p5 ∨ (((True ∧ p2) → (p2 → p2)) ∧ (((p4 → p3) ∨ (p1 ∧ p5)) ∨ True))) ∧ True) ∨ p2) ∧ (True → (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191318516472838984434265577088 : (((False ∧ True) ∨ (((p3 ∧ p1) ∨ (p4 ∧ p4)) ∨ False)) ∨ (False → (((p5 ∨ p3) ∨ (p5 ∧ (p5 → p3))) ∧ ((True ∧ (p3 ∧ p4)) ∧ p4)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702942512327699944166352993367 : ((((((False ∧ False) ∧ p4) ∨ (((True → p4) → p5) ∨ False)) ∨ ((((((p3 ∧ p3) ∨ p1) ∧ p3) → True) → (p3 → True)) → (p4 ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252535844072284852496138832821 : ((p5 → p2) ∨ ((p1 ∧ ((p3 → p4) ∧ (True ∨ p2))) → ((((p4 → p1) → (p4 → p3)) ∨ (True ∨ p2)) ∨ ((True → (p1 ∨ p2)) → p3)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256455912182478109066557666821 : ((False ∨ p4) → ((((False ∧ p4) → ((((True ∨ p3) ∨ ((p5 ∧ p3) → p2)) ∧ (p4 ∨ (p3 ∧ True))) ∧ (False ∧ (p1 → p1)))) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322574684582495368390814130362 : (p5 ∨ ((p4 ∨ ((p3 ∨ p3) ∨ (((p3 → (True ∨ p2)) ∧ (p5 ∨ p1)) ∧ ((((p1 ∧ True) → (False ∨ p1)) ∧ p1) ∧ (True ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142537090534153126683207777420 : ((True ∨ (((((p5 ∨ (p5 → False)) ∨ p2) → p1) ∨ True) ∨ (p5 → (True ∧ (p5 → ((p4 ∧ (p1 → p5)) ∧ p1)))))) → ((p1 ∧ p2) ∨ True)) := by
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
theorem thm_5_vars_53781755157040037800665761581 : ((((p1 ∧ (((p3 ∨ False) ∧ p1) ∨ (p5 ∧ p2))) ∨ p1) ∨ (True ∨ ((p2 ∧ ((False ∧ ((p2 → (p2 → True)) ∨ True)) ∧ True)) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677203743898367030710967246379 : ((((((True ∨ (p4 → (p3 ∧ (((((p4 ∨ (p5 → p1)) → p4) ∨ False) → False) ∨ p5)))) → p3) ∧ p1) ∨ ((p5 ∧ (False → p4)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635441358938345350234093971000 : (((((p5 ∧ ((False → ((False → p2) ∧ (p5 ∧ (p3 ∨ (p1 ∧ ((p2 → True) ∨ False)))))) → p2)) ∧ (p2 ∨ ((True ∧ p4) ∨ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148689505693966388949948200932 : (((p1 ∧ (p2 ∨ (False ∨ ((p5 → p1) ∨ p2)))) ∨ ((p5 ∧ p2) → (((p4 → (p1 → p2)) → False) → p2))) ∨ (p5 ∧ ((p5 → p3) ∧ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309784994055658708769662169932 : (p2 ∨ (((p1 ∨ (p1 ∧ ((p1 ∧ (p5 → False)) ∧ (((p1 ∨ p3) ∨ ((p5 ∧ p2) → p2)) ∨ p1)))) ∨ True) ∨ (((p4 → p5) ∧ False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149934671297522402458702882641 : ((p3 ∨ ((p1 ∨ (p1 → True)) → ((p1 ∧ (((True ∨ p1) ∧ ((True ∨ p5) ∨ p2)) ∨ p3)) ∨ (p5 → p3)))) ∨ (((p5 ∧ p3) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209574765203831093836152675913 : ((p5 → ((p3 ∧ p1) → (False ∨ p1))) → (((((p3 ∨ ((p3 ∧ p3) → True)) → p1) ∧ ((p1 → True) ∧ p1)) ∨ (p2 → (p2 ∨ p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774149374180812917314253504593 : (((False ∨ (((True ∧ ((p4 ∨ (p5 → p1)) ∨ (False ∨ p1))) ∧ (True ∨ (p1 ∧ ((p5 ∨ (p2 → (p3 → p5))) ∧ True)))) → (p1 → p1))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h16 =>
          -- One of the premise coincides with the conclusion.
          exact h11
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h25 =>
          -- One of the premise coincides with the conclusion.
          exact h20
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h35 =>
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h36 =>
          -- One of the premise coincides with the conclusion.
          exact h31
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68079548055966733776020728812 : ((p2 → (p3 ∨ ((p5 ∨ p5) ∨ ((((p2 ∧ p3) ∧ False) ∧ ((p3 ∧ (p2 → (p2 ∨ (p1 ∨ (False ∨ p3))))) ∨ p5)) ∨ (False ∨ p2))))) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301611211253607375859054510597 : (False ∨ (((p3 ∨ True) → p3) → ((False ∨ (p1 → False)) ∨ ((False ∨ ((p2 ∨ p1) → p3)) ∨ (((False ∧ True) ∧ ((p5 ∧ p2) ∧ p4)) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232073742610634468800222453775 : (((p4 ∨ p2) → False) → ((p4 ∧ ((p4 → p3) ∨ ((p4 ∨ (p2 ∨ (True → p1))) ∨ ((p3 → ((p4 ∨ p3) ∧ p1)) ∨ False)))) → (True ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h11 : (p4 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h12 := h1 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h15 : (p4 ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h16 := h1 h15
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h18 : (p4 ∨ p2) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h3
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h19 := h1 h18
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h22 : (p4 ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h23 := h1 h22
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52538617762396472452217285617 : ((((p4 ∨ (((p2 ∨ ((p5 ∧ p4) ∨ p5)) ∧ (p1 ∧ False)) ∧ False)) ∨ False) ∨ ((p4 → ((True → False) → p1)) ∨ (p5 ∨ (p4 ∨ p2)))) ∨ p5) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310175005594787045274063540772 : (p2 ∨ (((p3 ∧ (p3 ∧ (((p4 ∧ False) ∨ p1) ∨ (False ∧ False)))) ∨ True) ∧ (((False ∨ p5) ∧ False) → (p5 → (p1 ∧ ((p4 ∧ p3) ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h17 =>
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179458458544112716277085019740 : ((p5 ∨ ((p3 → p2) → (p3 ∨ ((p2 ∧ p1) ∧ ((p1 → p1) → p4))))) ∨ (((p4 → False) ∧ ((p1 ∧ False) → (p4 ∧ (p1 ∨ p4)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62373032631774086261622765861 : ((p3 ∧ (((p3 ∨ (True → p4)) → ((p3 ∧ (True ∨ (p5 ∧ ((p4 → p4) ∧ False)))) ∨ p2)) → (p2 → ((False → (False ∧ False)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50135980485625840312769773014 : (((p5 ∨ ((p5 ∨ p4) ∧ (((((p5 → ((p1 → p3) → False)) ∨ False) ∨ p1) ∧ p5) → (p5 → False)))) ∧ ((False ∧ p2) ∧ (False ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64281267109690851110864115254 : ((False ∨ (p1 → ((False → (p2 → p5)) ∧ (False ∧ ((p3 ∧ (True ∧ ((((p4 ∨ (p4 ∨ True)) ∨ p4) → (True → False)) ∧ p5))) ∨ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60363080219658564892959029503 : (((p3 → True) → ((((((p1 ∧ p5) → p4) → False) → (p4 ∧ (p3 → ((((p4 → p5) ∨ p5) ∧ p5) ∧ (p5 ∧ p5))))) → p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178572339429904761236551530130 : (((p3 ∧ (False ∧ (p5 ∧ (p4 ∨ p1)))) ∧ (False ∧ ((p3 ∨ True) ∨ False))) ∨ (((p3 ∧ False) ∨ (True → p5)) ∨ (((True ∨ p2) ∧ False) → p3))) := by
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
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52803718367072901236744348193 : ((((True → (p2 ∧ (p3 → (p5 → (p1 → p2))))) → ((p1 ∨ True) ∧ False)) → ((p1 → ((False → (p2 → (p3 ∨ True))) ∧ True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228268932836191285405910695586 : ((p5 ∧ (p4 → p2)) ∨ (p5 ∨ ((((p5 ∧ p1) ∨ True) ∧ (((p5 → ((True ∨ p3) ∧ (False → True))) ∨ ((p4 ∧ True) ∨ p1)) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157359812194929070966357832077 : (((p1 → ((((p3 ∨ (p4 ∨ p5)) ∧ (True ∧ p2)) ∧ (p2 ∧ p5)) ∨ (True ∨ (p4 ∧ p1)))) → p5) ∨ ((((p2 → p3) ∨ p4) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



