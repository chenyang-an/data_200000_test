variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45348898316710966395272688526 : (((p4 ∧ (((p3 ∧ ((((p5 → (p2 ∧ False)) → p4) ∨ False) ∧ p5)) → (p1 ∨ (p1 → ((p4 ∨ p4) → (p4 ∨ p4))))) ∨ p3)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320430275767040330436164720590 : (p4 ∨ ((p1 ∨ p1) → (((((True ∨ (((p4 → p2) ∧ p5) ∨ (p3 ∧ (p1 ∧ (True ∨ (p3 ∨ p2)))))) ∧ p5) ∨ False) ∨ p1) ∧ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327867047199782539802506406645 : (True → (((p2 ∧ p4) ∨ (((True ∨ (p4 → True)) ∨ ((p4 ∧ p2) ∧ ((p2 → (((p4 → p2) ∧ p5) ∨ p2)) → True))) → p2)) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319279007168980467555274230957 : (p4 ∨ ((((p5 → True) → (False ∨ p4)) → ((p4 ∨ ((p2 → p3) → p4)) ∨ (p3 ∨ p4))) ∨ (((((p4 ∧ p2) → p4) ∧ p1) → p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112018391308711367411965247817 : (((((False → False) ∨ p2) ∧ ((True ∧ (p5 → (p1 → (p5 ∨ True)))) → (((p5 ∧ p1) ∧ p5) ∧ (False ∨ (True → p4))))) ∨ p5) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261387997772064577448601001291 : ((p5 → p1) → ((p5 → (p3 → ((((((p4 ∨ True) ∨ (p1 ∨ p5)) ∧ p3) → (p4 ∧ (p5 ∨ False))) ∨ (p1 ∨ p4)) ∨ p1))) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225874511643036275671939524335 : (((False ∧ p5) ∨ p4) ∨ ((p3 ∨ ((((False ∨ (((False ∨ p5) ∧ ((p5 ∧ p5) → p2)) ∨ p5)) ∧ True) ∧ (p4 → (p5 ∨ p3))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217079851822009667989517095992 : ((((True ∧ True) ∨ p5) ∨ True) → ((p4 ∧ (p5 ∨ (p1 → p2))) ∨ ((((True ∨ ((p3 → p3) ∧ (p3 ∨ p3))) ∨ p3) → (p4 ∧ p5)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h7 : ((True ∨ ((p3 → p3) ∧ (p3 ∨ p3))) ∨ p3) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h8 := h6 h7
      -- We need to get the right conjuct of h8 based on <expert-advice>.
      let h9 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : ((True ∨ ((p3 → p3) ∧ (p3 ∨ p3))) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h15 := h13 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683458909825680505425346567206 : ((((p2 → (((((True ∨ False) ∨ p3) ∨ (p1 ∧ ((False → p2) ∧ (p2 ∧ p5)))) ∨ True) → p5)) ∧ ((p2 → ((p5 → p5) → p3)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230144369254261856540882246355 : (((p4 ∧ p2) ∧ True) → ((p3 ∨ ((p1 ∧ False) ∨ (False ∧ p5))) ∨ (False → ((((False ∨ p5) → p5) ∨ (p1 ∧ ((p1 ∨ p5) → p5))) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115935552053454136045548906727 : (((p4 ∧ (False ∧ (p2 ∨ p2))) ∨ ((True ∨ ((((p3 → p1) → (p5 → p3)) ∨ p3) ∧ True)) → (p5 ∨ ((True ∧ p3) ∨ True)))) ∨ (False ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
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
theorem thm_5_vars_354929855747439487349627356689 : (p5 → ((p3 ∨ ((((p2 ∧ p4) ∨ p3) ∨ False) → ((((p3 → ((p2 ∨ p5) ∨ True)) ∨ p4) ∨ p1) → (p2 → (p5 ∧ (False ∨ p5)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741322316516529762393170523235 : ((((p4 ∨ p5) ∨ (True ∧ (False ∧ ((((True ∨ (p1 ∨ p5)) → (p4 → (True ∧ True))) ∨ (((p2 ∧ False) → False) → (p3 → p4))) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114230030761550299754295908967 : (((p1 ∧ (p4 ∧ (p2 ∨ ((p5 ∧ (p1 ∧ (p2 → True))) → ((False → (p1 ∨ (p1 ∨ p4))) ∧ p1))))) → (False ∧ (True → p2))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247512415592973375958322643948 : ((False ∨ p3) ∨ (p1 ∨ ((p3 ∧ (False → (p3 → (p1 → p3)))) ∨ ((False ∨ True) ∨ ((False ∧ (p2 ∨ p1)) ∧ (p3 ∧ ((p5 ∧ p1) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156668002978694058736628001035 : ((((((False ∧ (p2 ∧ (p3 → (True → (p4 ∨ (p4 ∨ p4)))))) ∧ p1) ∨ p4) ∧ (True ∧ p1)) ∧ True) ∨ (False → ((True ∨ (False → p2)) ∧ False))) := by
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
theorem thm_5_vars_186645338366092330646157036430 : (((p5 → ((p4 ∧ (False ∨ (False ∨ p3))) ∨ p5)) → (p5 → p3)) → ((((False ∨ (p2 → p5)) → (False ∧ p4)) ∨ p2) ∨ ((False → p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317931486193245766904058982944 : (p4 ∨ ((p1 ∨ ((((((p3 ∨ p2) ∨ p3) ∧ p5) ∨ ((p5 ∨ p1) → ((p1 ∨ p1) → (p2 → (True ∧ (p5 ∧ p3)))))) ∧ p4) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160849923911815575523501164402 : (((((p4 ∨ p4) ∨ True) → p5) ∧ ((p4 → (p4 → p1)) ∨ ((p4 ∨ ((p5 → p3) ∨ p3)) ∧ p4))) → (p5 ∨ (True → (True ∧ (p5 ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∨ p4) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((p4 ∨ p4) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : ((p4 ∨ p4) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : ((p4 ∨ p4) ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120801287931513227428093881288 : ((((False → ((p4 ∧ (True → p5)) ∧ ((((p4 ∧ p3) ∨ p4) ∨ p4) ∨ (p3 → p1)))) ∨ ((True ∨ p2) ∧ (True ∨ p1))) ∨ False) → (p5 → p5)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h2
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h12 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h13 =>
          -- One of the premise coincides with the conclusion.
          exact h2
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326839247541199815797267829615 : (True → (((((((p3 → p2) ∧ p4) ∧ ((p2 ∨ False) → p5)) ∧ p4) → ((p3 ∧ p2) ∧ ((((p5 → p5) ∧ p2) → True) ∨ p2))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249623197552434816964261185596 : ((p5 ∨ p3) ∨ (((False ∧ p4) → False) ∧ (((p1 ∨ (p3 ∨ p5)) → ((((p5 ∧ p2) ∧ p2) ∧ (p3 ∧ (p5 → (p1 ∧ True)))) ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39740400509531244046316593290 : (((p5 ∨ (p2 ∨ (((p3 ∧ (p2 → p4)) ∨ ((True ∧ (p2 → ((False ∧ p2) ∨ ((p1 ∨ (p1 ∧ False)) → True)))) ∧ p2)) ∧ p2))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162051370917142112212805469457 : ((p5 → ((True ∨ ((p1 ∨ ((p1 → p3) ∧ (p4 ∧ (p4 ∧ (p4 → (False ∨ p4)))))) → False)) ∧ p2)) → (True ∧ (p3 ∨ ((p2 ∧ p5) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69071972787814671125745356888 : ((p5 → ((((p1 ∨ (((p1 → p5) ∨ (True ∧ (p3 → p3))) ∧ (p3 ∨ (p4 → (p5 → (p1 ∧ p3)))))) ∧ p4) ∧ (p2 ∨ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113072855327543892013101901287 : (((p3 ∨ ((True ∨ p5) ∨ (p5 → (((((False → False) ∧ True) ∧ ((((p4 ∨ p5) → p4) → p3) → True)) ∨ True) ∨ p3)))) → p5) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134582575444374690360041210545 : (((((p2 → (((((p5 ∨ True) → p1) ∨ ((p5 ∨ p1) → p5)) → (p4 → p5)) → p1)) → False) ∨ (p4 → p1)) → p3) ∨ (p1 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154741696093077583796673127413 : ((((((False ∧ p3) ∨ False) ∨ (p5 ∨ True)) ∧ (((p4 ∧ False) ∨ (p2 ∧ True)) → p3)) ∨ (p5 ∨ True)) ∧ (True → (p4 ∨ ((p3 → True) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356041233717129802002497440432 : (p5 → ((True ∧ (p2 → ((((p5 ∧ ((True → (p1 → True)) → p1)) ∨ p3) ∧ p3) ∧ (True ∨ (p5 ∧ p4))))) ∨ (False ∨ ((p1 ∨ p2) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204590494817652238340821055018 : ((((False ∨ p5) ∨ (p2 ∨ False)) ∨ p3) ∨ ((False ∨ (False ∧ ((p1 → (p2 ∨ ((p1 ∧ (True ∨ ((p5 ∧ p1) ∨ False))) ∨ p1))) ∧ False))) → p3)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680470150758994130645982646054 : (((((p1 → (((p4 ∨ ((p3 → p4) → False)) → (False ∧ p5)) ∨ p5)) → ((p1 ∧ (p5 → False)) ∨ p2)) → (p4 ∧ ((True → p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249626084762440514936562445620 : ((p5 ∨ p3) ∨ ((True ∨ True) ∧ (((((False ∧ (p3 ∨ False)) ∧ p4) ∨ True) ∨ ((p2 ∨ p4) ∧ (((False ∨ (p1 ∨ p5)) ∨ p3) ∨ p3))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_66117873368881847530267764605 : ((p5 ∨ ((False ∨ ((p4 ∨ ((((p2 ∨ p4) ∨ p2) ∧ p5) ∧ (p2 ∧ ((p5 ∨ p2) ∨ p2)))) ∧ ((p4 ∧ p4) ∨ (False → p4)))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198376786591245239218473686365 : ((p3 ∧ ((p3 ∨ ((p5 ∨ p5) → False)) → False)) ∨ ((False ∨ (((((((p2 → p2) → True) → (p3 ∧ p5)) → p3) ∨ p1) ∧ p5) → True)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41163271001439383773546945613 : ((((True → (False ∨ ((((((p4 → p3) ∨ False) ∧ True) ∧ False) → ((p1 ∧ p4) ∧ p4)) ∧ (p1 → p5)))) ∨ (False ∧ (p3 → False))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707795068431278356991511292950 : ((((False ∧ ((p1 → ((p4 ∨ p2) ∧ p5)) → p3)) ∨ (((True ∧ True) ∧ ((False ∨ False) ∨ ((p4 ∨ p4) → p3))) ∨ ((p4 → p3) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135219053055152348060682627009 : (((((p2 ∨ p2) ∨ (((False → (p5 → p4)) ∨ (p1 → p4)) ∧ p5)) → (p2 ∧ ((p4 ∧ False) → p2))) → (p3 ∧ p2)) ∨ (False → (p2 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336114518957775496935816985244 : (p1 → (((((p4 ∧ (p1 ∧ p4)) → ((False ∧ p2) ∧ (p4 ∨ ((((p3 ∨ (True → (False ∧ p3))) ∨ p2) ∧ p5) ∨ p5)))) → p4) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49440553939162911384368555417 : (((((p4 → (p5 → (True ∨ ((((False → (False ∧ p2)) ∧ p5) ∧ True) ∧ p5)))) → (p2 ∨ (p3 → p2))) ∨ p4) → ((p3 ∨ True) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49333395476189083625089188632 : (((p5 ∨ (True ∧ ((((True ∧ (p1 ∨ False)) ∨ (True → (((p5 → p5) ∨ False) → (p1 ∨ p4)))) → p4) ∨ p1))) ∨ ((True ∨ True) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46677377750683768810501099558 : (((p1 ∨ (p5 ∨ ((((True → ((p2 ∧ p3) ∧ p4)) → ((p2 ∨ (True ∧ p4)) → (False ∨ (p2 → True)))) ∧ p1) ∨ p4))) ∧ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638158536537261017315323073998 : (((((((True ∧ p2) → (True ∧ (p1 ∧ p1))) → p4) → (True → (((p1 → False) → p5) → (p2 → ((p2 ∧ False) → (p4 → p4)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185428122337815467902867957741 : ((False ∨ ((False ∨ ((p3 ∨ (p3 ∨ p1)) ∨ (True ∨ p2))) ∧ p5)) ∨ (((False ∧ (p4 → True)) ∧ p3) → ((p3 ∨ ((p3 → p2) → True)) ∧ p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114621378374681957628600459772 : (((((p2 ∨ (p1 ∧ (p1 → (p4 ∧ ((False ∧ p5) → p5))))) → (p3 ∨ p2)) ∧ p3) ∨ (p4 → ((False ∨ (p1 ∨ p4)) → p4))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114502849638168850265011223929 : ((((False → ((p1 → p4) ∧ True)) → ((p5 ∧ (p3 ∧ False)) → (False → ((p5 ∨ p2) → p5)))) → (((True → p2) ∧ p2) ∧ True)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764226909214809065383559451474 : (((p4 ∧ (((p3 → (((p2 ∧ p2) ∧ (((p3 → p3) ∨ p2) ∨ ((p2 → (True ∨ (p4 ∧ True))) ∨ (p1 ∧ p2)))) ∨ p1)) ∧ p3) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624404617600288706637879485146 : ((((p3 ∨ (p3 ∧ ((((True ∧ p5) ∧ p1) ∨ (((p1 ∨ p5) ∨ p1) → ((p4 → False) ∧ (p5 → False)))) ∧ ((True ∧ p2) → p3)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_56830367147579957354204886825 : ((((p2 → p3) → True) ∧ ((((False ∧ True) ∧ ((p2 ∧ (((False → p4) ∨ p4) ∧ (p1 ∧ p2))) ∧ ((False ∨ p5) ∧ p5))) ∧ p2) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_973650633541324238303508979323 : ((((p5 ∨ True) → ((((True ∧ p2) ∨ False) ∧ ((p3 ∨ (((p5 ∧ p5) ∨ ((p5 ∨ (p2 ∨ p5)) → False)) → (p2 ∧ p2))) → p1)) ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40354336908422029603959418902 : (((((((((p1 ∨ ((p4 ∨ True) ∧ ((p2 ∨ (p1 ∧ p1)) ∨ p5))) → p4) → (p2 ∧ False)) → (p3 ∨ p4)) → False) → p3) ∨ True) ∨ p4) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149373362360068671782797691707 : (((p1 → p5) → (((p4 → (p5 ∧ p5)) ∨ p5) → ((p4 ∧ (True ∨ p1)) ∧ ((p4 → (p1 → p2)) ∨ p1)))) ∨ (False → (p5 ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733489843087690383084464712400 : ((((p4 ∧ p2) ∧ (False ∧ (p1 ∧ (((p3 ∨ (False → (False → p3))) ∧ ((p2 → (((p5 → p3) ∧ True) → (p2 → False))) ∨ p3)) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58068970074113102266539545658 : (((False ∧ p4) ∧ ((((((p5 ∨ False) ∧ True) → (p2 → (p2 → p2))) → p1) ∧ (((False ∨ ((p4 ∨ p4) → p4)) → True) ∨ p5)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682994267888543672123068570263 : (((((False ∨ p4) → (p4 ∧ (p3 ∧ (True ∨ ((((True ∨ p2) ∨ (p4 → False)) ∧ True) ∨ p5))))) ∧ (((p5 ∧ p4) → p1) → (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57256380200839970842026367239 : ((((True ∨ p2) → p4) ∨ ((p1 ∨ (p3 ∧ (((False ∨ ((((p5 ∧ p2) ∨ p5) ∧ p5) → p2)) ∧ p5) → (p1 ∧ (p1 → True))))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247495138219910852971210758464 : ((False ∨ p3) ∨ ((((p3 ∨ False) ∧ p3) ∨ (p2 → False)) → ((((True ∨ (p1 ∧ (False ∨ p1))) ∨ p1) → (p2 ∧ (p1 → True))) ∨ (True ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305341694043867691965471519724 : (p1 ∨ (((((p3 → p5) ∧ p1) → (p3 ∨ True)) → ((((p3 ∨ p3) ∨ p3) ∧ p3) ∧ (p4 ∧ False))) → ((((p4 ∨ True) ∨ p2) → False) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → p5) ∧ p1) → (p3 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198379565045991424258845700777 : ((p3 ∧ (((p5 ∨ p1) ∧ p2) ∨ (p1 ∨ False))) ∨ (((p3 ∨ (p2 ∧ ((((p4 → True) ∧ True) → p2) ∧ p3))) ∧ p5) → ((p3 ∨ p3) ∨ p2))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192663174818191445571693959266 : ((((((p4 ∨ p2) ∧ p3) ∨ (p2 → p1)) → True) → False) → (p5 ∧ (((False ∧ (p5 ∧ ((((p5 ∧ p5) ∨ p1) → p4) ∧ p5))) ∧ p4) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∨ p2) ∧ p3) ∨ (p2 → p1)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243764918193322072003542835148 : ((p5 → p5) ∧ ((((((p2 ∨ p4) → (p4 ∨ False)) ∧ p3) ∧ p3) ∨ (p5 ∨ ((((True → False) ∧ ((p5 ∧ p2) → True)) → False) → p5))) ∨ True)) := by
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
theorem thm_5_vars_57942859574455208950161480641 : (((False → (p1 → p4)) → ((((p3 ∧ ((False ∧ p4) ∧ p4)) ∨ (p4 ∨ (p4 ∨ True))) ∧ (False → ((p2 ∧ p5) ∨ p4))) ∧ (p5 → p5))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224266587885345038241997127726 : ((False → (True ∧ p4)) ∧ (((p2 → p3) → ((p1 ∨ (p1 → p2)) ∧ False)) → ((p3 ∧ (((p2 ∨ (p5 ∧ (p1 ∨ False))) ∧ p1) → p1)) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225523834798822551655980875026 : (((True → True) ∧ p1) ∨ (((p3 → p4) ∨ p1) → (p5 → ((p3 ∧ True) → (((((p2 → p4) ∨ p2) → p2) ∨ p3) ∧ (True ∧ (p3 → p5))))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328289526996993608968894934732 : (True → (((p4 ∨ ((p3 ∧ p1) ∨ (p3 ∧ (p3 → ((p3 ∧ True) ∧ p4))))) ∨ ((True ∧ p4) ∨ (p4 ∧ p2))) ∨ (True ∧ (False → (p2 ∧ False))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147279791334706732861574996622 : (((((False ∨ p5) ∨ ((((False ∧ p2) ∨ (p4 → (p4 ∨ p2))) → False) ∨ ((p2 → p3) ∨ True))) ∨ p3) ∨ p5) ∨ ((p1 → p1) → (p3 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_327135220416133420155611282998 : (True → ((False ∧ ((((p4 ∨ p5) → p3) ∨ True) ∧ ((((p2 → False) ∨ (p2 → p4)) ∧ p1) → (((p2 ∨ (p5 ∧ p5)) ∧ p2) ∨ p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158363870916904812358762338657 : (((p2 ∨ p1) ∧ ((((p5 ∧ False) → p1) ∧ (p5 ∨ (p2 ∨ p1))) → (((True ∧ p4) → p3) ∧ p5))) ∨ (True → ((p1 ∨ (p2 → p2)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656870034185954947071317673979 : (((((p2 ∨ (p4 ∨ (p3 ∨ True))) ∧ ((p5 ∨ p1) ∨ ((False → (p5 ∧ (p5 → (p4 → ((p2 ∧ False) → False))))) ∨ p4))) ∨ (False ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66569290775807019762491272427 : ((True → ((p4 ∧ (((True ∧ p4) → ((((p2 ∨ p4) ∧ (p4 ∨ True)) ∨ (p4 ∧ False)) → (p2 ∨ (p5 → p2)))) → p3)) ∨ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336207872585643397138450790307 : (p1 → (((((p3 ∧ (p4 ∧ (p2 → (((True → p1) ∧ p5) → ((p5 → ((p5 → p3) ∧ True)) ∧ p2))))) ∨ p5) → p4) → (p5 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165668974344590400788073052886 : (((p4 ∨ (p1 ∧ ((p1 ∧ False) ∧ p1))) ∨ (((p5 ∨ (p2 → p1)) ∨ False) → (p1 ∨ p5))) ∨ ((False ∧ False) → ((False ∨ (p5 ∧ p4)) ∧ p4))) := by
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
theorem thm_5_vars_60071606386850962609591893620 : (((p2 ∨ p3) → ((((((p2 → (((True ∨ True) ∧ p4) ∧ True)) ∨ (p1 → p1)) → (p5 ∧ p3)) ∨ True) ∧ True) ∨ (p4 → (p3 ∧ p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
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
theorem thm_5_vars_136115374513347833068895194212 : (((True ∧ (p5 → ((True ∧ (p2 ∧ True)) ∧ p5))) ∨ (((p4 ∨ p3) → ((False ∧ False) → ((p4 ∧ p5) → p1))) → p1)) ∨ (True ∧ (p3 ∨ True))) := by
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
theorem thm_5_vars_110719487474712865770136514172 : (((((p4 ∨ ((False ∨ p2) ∨ ((True ∨ ((p2 → (p2 → p3)) ∨ False)) ∧ (p4 ∧ (p2 ∧ False))))) ∧ (p2 ∧ False)) ∧ p4) ∧ p2) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174837402909785911476551477436 : (((p4 ∧ p2) ∨ (p5 ∨ ((p1 → (p2 → p1)) ∧ (((p5 ∧ False) ∧ p3) ∨ True)))) → ((p2 → (p4 ∨ p2)) → (((p4 → p2) ∨ p3) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h14 := h12.left
        let h15 := h12.right
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110732492096196919018896465874 : ((((((p4 ∧ (((p1 ∨ True) ∨ (p2 ∧ False)) ∧ p4)) ∨ False) ∧ (((p4 → ((p2 ∧ False) → p2)) ∨ p4) ∨ p5)) ∧ p3) ∧ p1) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351854798387052624597612104789 : (p4 → (((p2 → True) ∨ (p4 ∨ ((p2 ∨ True) ∨ (True ∧ (p1 ∨ True))))) → ((p3 ∧ (False ∨ p1)) ∨ (p4 ∨ (p2 → ((False → p3) → p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216571886617140505203422085961 : ((((False ∨ p4) ∧ p5) ∧ p5) → ((p1 ∧ (True ∧ p5)) → (p3 → ((p3 → (False ∨ ((False ∧ (True ∨ ((False ∧ False) ∨ True))) ∧ False))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55579847538639849665673115130 : (((p1 ∨ (p1 ∧ ((p4 ∧ p3) → p2))) → (((((p4 ∧ ((p4 → p4) ∨ (p2 → False))) ∨ p5) ∧ (p2 ∨ p3)) → (p2 ∨ True)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68138034462824137114963286480 : ((p3 → ((((p4 → p3) ∧ (True → ((((p1 ∧ (p2 ∧ p5)) ∨ ((True ∧ p2) ∨ p3)) → ((False → p4) → p2)) → p4))) ∨ True) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587828229052115374372357988218 : ((((((((True ∧ (False ∨ (((p5 ∧ p5) ∨ False) ∧ p5))) ∧ True) ∨ ((p2 ∨ (p3 ∧ p5)) → (False ∧ p5))) ∨ (p2 ∧ True)) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188165806317903128763769351976 : ((((p4 → (p1 ∨ ((True → p4) → False))) → p4) ∨ True) ∧ (((False ∨ (p1 → (True ∨ p3))) ∨ p3) ∨ ((p3 ∨ (p1 → (False ∧ p3))) → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249167913158175127471331924603 : ((p4 ∨ p3) ∨ (((p2 ∨ (((p5 → p3) ∨ p5) → (((False ∨ ((((True ∨ True) ∧ p2) ∨ (p3 → p5)) ∧ p1)) ∨ p3) ∨ p1))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55946260591998298418636684847 : (((p4 → ((p4 ∧ p1) ∨ p1)) ∧ (p4 → ((p5 ∧ ((p3 → p4) ∨ ((True ∧ p1) → ((p5 ∨ ((p4 ∨ False) ∧ p3)) → True)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214803109895551566405505518515 : (((p2 ∨ p2) ∨ (p4 ∧ p1)) ∨ ((p1 → ((True ∧ False) ∨ p1)) ∨ ((p3 ∨ (p5 ∨ (p2 ∨ p1))) ∨ (p4 ∧ (((p5 ∧ p4) → p1) → p2))))) := by
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
theorem thm_5_vars_65200548677822694958893678694 : ((p3 ∨ ((((((True → p1) ∨ (False ∨ ((False ∧ p3) ∨ (p2 ∨ (p3 ∧ (p3 → p5)))))) ∧ False) ∧ (p3 ∨ (True ∧ p3))) ∨ True) ∨ p1)) ∨ p2) := by
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
theorem thm_5_vars_357896233648875757235721940741 : (p5 → (p5 ∧ (p1 ∨ ((p3 ∨ (p1 ∧ (p2 ∧ p4))) ∨ (p2 ∨ (True ∨ (True ∨ (p3 → ((False ∧ p1) ∨ (p1 → ((p4 → p4) → p2))))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_261087028569250648731943224224 : ((p4 → p3) → (((((((p2 → p5) ∧ p2) ∨ False) ∨ True) → ((p4 ∨ (p5 ∨ ((p5 → p4) ∨ p2))) ∧ p4)) → p3) ∨ ((p4 ∨ p2) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p2 → p5) ∧ p2) ∨ False) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66497209566812317385315068781 : ((True → (((False ∧ p4) ∨ ((((p4 ∧ True) ∧ p3) ∨ ((p5 ∧ (((False ∧ ((True → False) ∨ p5)) ∧ p2) ∨ p2)) ∨ True)) ∨ True)) ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330463645920617765232280654414 : (True → (p3 ∨ (p4 ∨ (((False ∨ ((p3 → ((p1 ∨ p2) ∧ p3)) ∨ ((p1 ∧ (True → p3)) ∨ (False ∧ p2)))) → ((p5 → p1) ∨ p1)) ∨ True)))) := by
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
theorem thm_5_vars_52099022282355100712740544885 : (((((p3 ∨ p5) ∨ (p5 → (False ∨ (p2 ∧ ((p5 ∧ p4) ∨ (p1 ∨ p4)))))) ∨ p4) → ((p4 ∨ ((p3 → True) → p5)) ∨ (p3 → True))) ∨ False) := by
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199611633014477487351080603301 : ((((p5 ∨ ((p2 ∧ True) ∧ p2)) → p4) → p4) → (p4 → ((((p4 → (p1 ∨ ((p5 ∧ p3) ∧ p3))) ∧ (p3 ∨ (p3 ∨ p3))) → p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165356821316195412768880730847 : (((p2 ∨ (p4 ∨ (p2 ∨ (((p1 ∧ p2) ∧ (p5 → p1)) → p5)))) ∧ (p5 → (p5 ∨ p1))) ∨ ((True ∧ ((p4 ∧ p3) → (False → p1))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720618462684921344750441255349 : ((((((True ∧ p5) ∨ p5) → False) → ((p3 ∧ ((p4 ∨ True) ∧ p2)) ∨ (p2 ∨ ((p2 ∨ (p5 ∧ p3)) ∧ ((p3 ∨ (p3 ∧ p1)) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94504449892732712007834520796 : ((p2 ∧ (True → (((((p2 → p5) → (p5 → (False → False))) → p4) → ((False ∨ (p4 ∨ (p1 → p5))) ∧ p2)) ∧ ((p3 → p4) ∧ False)))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227427233630751982639661095512 : (((p5 → p1) → p5) ∨ (((((False ∨ (p5 → (((p3 → p1) ∨ (p3 ∨ p5)) ∧ p3))) → p2) ∧ (((p4 ∧ p1) ∧ False) ∨ p2)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303759102723593755270587132480 : (p1 ∨ (((((((p4 ∧ False) ∧ False) ∨ ((p5 ∧ p1) → (p4 → False))) ∧ ((p3 ∨ (p1 → p5)) → p2)) → ((True ∧ p5) → p4)) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_838624530310999156749012183867 : ((((((False ∨ (p1 → (((p1 ∧ (p5 → p4)) → (False ∨ ((p1 ∨ (False → p4)) → p4))) ∧ p2))) → (True → p5)) ∧ (p4 ∧ p2)) ∨ p5) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False ∨ (p1 → (((p1 ∧ (p5 → p4)) → (False ∨ ((p1 ∨ (False → p4)) → p4))) ∧ p2))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h5
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h7
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207672047386544522395131278749 : ((((False → p5) ∨ (p3 → p1)) → p1) → (p3 ∨ (True ∧ (((p1 ∧ p2) ∧ (p3 ∨ (p3 ∧ (((p1 → p3) ∧ False) ∧ p4)))) ∨ (p2 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False → p5) ∨ (p3 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305309256392553650639861095374 : (p1 ∨ (((p4 ∧ False) ∨ ((p5 ∧ p3) ∨ (p4 ∨ (((False ∧ p2) ∧ p1) ∨ (True ∨ (p1 ∨ p4)))))) ∨ ((p2 ∧ (p4 ∧ True)) → (p5 → p2)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



