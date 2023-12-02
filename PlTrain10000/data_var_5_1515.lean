variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114311874600254237507057680398 : (((((p3 ∨ (p3 ∨ p2)) → (False ∨ False)) → ((p3 ∨ (p3 → (p2 ∧ (p1 ∧ True)))) ∧ p5)) ∧ (p2 ∧ ((p3 ∧ p5) ∨ p4))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216930247670698809116117275160 : (((True → (p1 ∨ p4)) ∧ p3) → (p1 ∨ (p2 ∨ ((p4 → ((p1 ∨ p2) ∧ p1)) ∨ (p3 ∨ ((False → p3) ∨ ((p2 ∨ True) ∨ (p1 → True)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179136259846598233281585820651 : ((p1 ∧ ((p1 ∨ p3) → (((p4 ∨ ((p3 ∨ True) ∧ p3)) ∨ p5) ∧ p2))) ∨ (p2 → (((p5 → (False ∧ p2)) → (p1 → p2)) ∧ (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303935178864648298056302410637 : (p1 ∨ (((p4 → ((True ∨ (p1 → (False → p5))) → True)) → ((p4 → ((p3 → p2) ∨ ((p4 ∧ ((False ∨ p3) ∨ p2)) ∧ False))) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_787883370550003592270608514382 : (((p4 ∨ (p2 → (False ∨ (((((p3 ∧ ((((p2 ∧ p1) → p5) ∧ p3) ∨ (p1 ∧ (True ∨ p1)))) ∨ p2) ∨ p3) ∨ (p1 ∧ p1)) ∨ False)))) ∨ p2) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184635890024085524210627884036 : (((p3 ∨ (p1 ∧ (False ∧ (p5 ∨ False)))) ∧ (p1 ∧ (p1 → p3))) ∨ (((p5 ∧ p1) ∧ p5) → ((p3 ∧ p5) ∨ (((p5 → True) ∨ p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60662344942467234748969242258 : ((True ∧ ((True ∨ ((p2 ∧ (p5 → (((p3 ∨ p1) ∨ True) ∧ p4))) ∨ (((p1 → p5) → False) → p2))) → (p2 ∧ (p3 ∧ (p4 ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230809337676373194166550492449 : (((False ∧ p1) ∨ p1) → ((((True → (((p1 ∧ p5) ∧ p3) ∧ p2)) ∧ p5) ∧ (p2 ∨ ((False → (p5 → p4)) ∧ (p1 → p3)))) → (p3 ∧ p1))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- False on the left can always be used.
      apply False.elim h20
    case inr h22 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h23 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h22
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h24 := h18 h23
      -- One of the premise coincides with the conclusion.
      exact h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- False on the left can always be used.
      apply False.elim h31
    case inr h33 =>
      -- One of the premise coincides with the conclusion.
      exact h33
  case inr h34 =>
    -- Conjunctions on the left can always be decomposed.
    let h35 := h34.left
    let h36 := h34.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h37.left
      let h39 := h37.right
      -- False on the left can always be used.
      apply False.elim h38
    case inr h40 =>
      -- One of the premise coincides with the conclusion.
      exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209474757232093675702988693053 : ((p3 → ((p1 ∧ True) ∧ (p2 ∨ p1))) → ((p3 ∧ ((p5 ∧ (True → p2)) ∧ (((p5 ∧ p2) → p5) ∧ (p4 ∧ (p4 ∨ p2))))) → (p2 ∧ p2))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h13 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h15 := h8 h14
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h19.left
  let h22 := h19.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h20.left
  let h24 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h24.left
  let h26 := h24.right
  -- Disjunctions on the left can always be decomposed.
  cases h26
  case inl h27 =>
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h28 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h29 := h22 h28
    -- One of the premise coincides with the conclusion.
    exact h29
  case inr h30 =>
    -- One of the premise coincides with the conclusion.
    exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107470618206626395270262858563 : (((p3 ∧ (p4 ∨ p2)) → (p3 ∧ (True ∧ ((p4 → ((((((p4 ∨ p1) ∨ True) → False) → p1) → (p5 ∧ p3)) ∨ True)) ∨ p4)))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_887196753046110755350454331182 : ((((((p3 ∨ (((False → (p4 → (p1 ∨ p3))) ∨ p2) ∨ ((False → p5) → p1))) → ((p5 ∧ p1) ∧ (p1 ∧ False))) → p4) → (p3 ∧ False)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (((False → (p4 → (p1 ∨ p3))) ∨ p2) ∨ ((False → p5) → p1))) → ((p5 ∧ p1) ∧ (p1 ∧ False))) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ (((False → (p4 → (p1 ∨ p3))) ∨ p2) ∨ ((False → p5) → p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h4
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126038087769270893191413067350 : (((p3 → True) → ((((((p3 ∨ p4) → (p3 ∨ p3)) → True) ∧ ((True ∨ p1) ∧ (p4 ∧ p1))) ∧ p4) ∧ (True ∨ (p5 ∧ p3)))) → (p1 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134695606407653092586830743369 : (((((p5 ∨ p1) ∨ (p5 → p2)) ∧ ((p2 ∧ (((p4 ∨ ((p3 ∨ p2) ∧ (p4 ∧ p5))) ∧ p4) ∧ True)) → True)) → False) ∨ ((p4 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180514899797416116432264110347 : (((p4 → ((p5 → p2) ∨ (p2 ∨ (False ∧ p4)))) ∧ (p3 ∨ (p3 ∨ p5))) → ((((p3 ∧ p3) ∧ (p3 ∧ p4)) ∨ True) ∨ ((p4 ∨ p1) → False))) := by
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
theorem thm_5_vars_217313718581322881721955776821 : (((True ∨ (p4 ∧ p2)) ∨ p1) → ((True ∧ ((True → False) ∧ (((False → (False ∧ (p2 ∨ p5))) → False) ∧ p4))) → (True ∧ (False ∨ (p3 ∧ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h12 := h5 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h20 := h5 h19
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303253776603515053175694974962 : (False ∨ (p5 → (((False ∧ False) ∧ (False ∧ p4)) ∨ (((((p3 ∨ (False ∧ True)) ∧ ((True → True) ∨ False)) ∧ (p3 → False)) ∨ (True ∨ False)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_600437908215103658624822592051 : ((((True ∧ (((p1 → (p3 → ((True → (p4 ∨ (False → False))) → (p3 → True)))) ∧ (True ∧ (p2 ∨ p2))) → (p1 ∧ (p2 ∨ p1)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322475786723620981970988156982 : (p5 ∨ (((p2 ∨ p2) ∧ (((True → p2) ∧ (False ∨ (True → ((True → p2) → (p3 ∨ (p1 ∧ (p4 ∧ (p1 ∧ (True → p5))))))))) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52905054509591362248249786321 : (((p1 → ((((True → (p2 ∧ p4)) → (False ∧ (p4 → False))) ∧ p2) → p4)) → (((False ∨ p2) ∨ (((p5 → p5) → False) → p2)) ∨ p1)) ∨ p5) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190489116310426114519786736920 : ((((((p4 → (p3 → True)) ∨ False) ∨ True) ∨ p3) → p4) ∨ ((((p1 → p3) → p2) ∨ ((p2 ∧ p3) → p3)) ∨ (((False ∨ p2) → p1) ∧ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190318306912157501591105609594 : (((((p2 ∧ (False ∧ p5)) ∧ p3) ∨ (p1 ∨ p3)) ∨ p1) ∨ ((p5 ∨ (((False ∧ p2) ∧ p2) → p5)) → (p4 → ((p3 → p4) ∨ (p2 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311926985841125183992108540937 : (p2 ∨ (p3 ∨ (((p2 → (p2 ∧ p5)) ∨ ((p5 → (p2 ∨ (p1 ∧ (p4 → ((p2 → False) → (((True ∨ p2) ∧ False) ∨ p5)))))) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197749650865736130615070170405 : (((False ∧ (p2 ∧ p5)) ∧ (p1 → (p2 ∧ p2))) ∨ ((p4 ∨ True) ∧ ((p1 ∧ (((p1 → p5) ∨ p3) ∧ (p1 ∨ p3))) → (p4 → (False → p4))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68921162981087392522109683898 : ((p4 → (p2 ∨ (((p5 → p1) ∧ (p1 ∧ ((((False → (p3 ∨ True)) ∨ False) → (p4 ∧ p3)) → ((False ∨ (p2 ∧ True)) ∨ p5)))) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44826207068218763911696651205 : ((((p4 → (True ∨ False)) ∧ ((((p1 ∨ (False → p4)) → ((p3 → p3) ∧ False)) ∨ p1) ∧ (((p4 ∨ (p3 → p5)) → False) ∨ p4))) → p1) ∨ p1) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (p1 ∨ (False → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h8
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h13 : (p1 ∨ (False → p4)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h15 := h6 h13
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198695669934574405475501859464 : ((p4 ∨ (p5 ∨ (((True ∨ True) → p4) ∨ p5))) ∨ ((p1 ∨ True) ∨ (((((False ∧ ((p5 ∨ p2) ∨ False)) ∨ p4) ∧ (p3 ∧ p3)) → p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148660697933996478090033466916 : (((p5 ∧ (p5 → (((True ∨ p3) ∧ p1) ∧ p5))) ∧ (((((True → p5) ∧ p5) ∨ p1) ∧ (p4 ∧ p2)) ∧ p4)) ∨ (((False ∧ p2) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57053181728750742944072023815 : (((p4 → (False ∧ p2)) ∧ (p2 → ((p2 ∧ p1) ∧ (((False → (p2 → (True → (True → (p4 ∨ ((True → p4) ∨ p1)))))) ∨ p5) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193981258309867453610293018239 : ((p3 ∨ ((p3 → (True ∨ p3)) ∧ ((p4 ∧ p5) → False))) → ((((False ∧ (p3 → p3)) → (p4 ∨ ((p4 ∧ p1) ∧ p3))) ∧ (p4 → False)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197444953098082475929911717710 : (((((p4 ∧ p5) ∨ p2) ∨ False) ∧ (p4 ∨ p4)) ∨ (((((True → (True ∧ (p2 → True))) ∨ p4) ∧ (p3 ∨ p2)) ∧ (p2 ∧ (p2 ∧ p4))) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h3.left
      let h25 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338415317089361118835232526732 : (p1 → (((p3 ∨ True) → (p5 → False)) → ((((p1 → True) → ((False ∨ p2) ∨ (p1 → True))) → (((p4 ∨ p5) ∧ False) ∨ (p1 → False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60085498480552568948420841135 : (((p2 ∨ p5) → (p1 ∨ ((((True → p5) → (p1 ∨ (p5 ∧ (p3 → (p1 ∧ False))))) ∨ (p1 ∨ (p3 ∧ p5))) ∧ (False ∧ (p5 ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10459557472041176497517886675 : (((p1 → ((((p3 ∧ p5) ∧ (False → p2)) ∨ (p5 ∧ p4)) ∧ ((p3 ∨ p5) ∧ (p3 ∧ (((p1 ∧ p5) → (p4 ∧ p4)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115259025346954895209153251468 : ((((p1 ∧ p2) ∧ ((((False ∧ True) → False) ∨ p4) → p1)) ∨ ((p5 → (p5 → (((p2 ∨ p1) ∧ p4) ∨ p5))) → (p5 ∧ True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324810127948624701609649137785 : (p5 ∨ ((False ∨ True) ∧ (((False ∧ (p1 ∨ (p2 ∨ p3))) → p5) ∧ (((False ∨ p2) ∨ ((p4 ∨ True) ∨ (p1 ∧ False))) → (False ∨ (p5 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
theorem thm_5_vars_731887430663970904810356263296 : ((((p4 → (p5 → p5)) → ((((((p1 → p5) ∨ p1) ∨ True) → p1) → p4) ∨ (((p5 ∨ p5) → (((False ∧ p5) → p3) ∨ True)) ∨ p1))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327203463966877031047173940113 : (True → ((p5 ∨ ((p5 ∧ True) → (((True ∧ p3) ∨ (p4 ∧ p5)) → ((((p4 ∧ p3) ∧ p2) ∨ p5) ∨ (p5 ∨ (False ∧ (p1 → p2))))))) ∨ False)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h2.left
    let h8 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h2.left
    let h13 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172103420728854370812558352655 : (((p4 ∨ ((((p2 ∧ p3) → False) ∧ (True ∨ True)) ∨ (p4 → False))) → (p5 → p2)) ∨ (((p4 ∨ (True ∧ ((False ∨ True) ∨ p4))) ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245731727471793604149674859965 : ((p3 ∧ p2) ∨ ((True ∨ ((True ∨ ((True ∨ p1) → p5)) ∨ p2)) ∧ ((True ∨ False) → ((False ∨ (((p1 ∧ (p2 ∨ p3)) ∧ p1) ∨ True)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1222487777651252727639689626 : ((True ∧ ((True → p2) ∧ (((p5 → ((p4 ∧ p4) ∧ False)) ∨ ((False ∨ True) ∧ True)) ∧ (p2 ∨ ((p5 ∨ False) ∨ (p4 ∨ True)))))) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h14 := h4 h13
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h19 := h4 h18
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h22 := h4 h21
          -- One of the premise coincides with the conclusion.
          exact h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h26 =>
      -- False on the left can always be used.
      apply False.elim h26
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h32 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h33 := h4 h32
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- False on the left can always be used.
            apply False.elim h34
        case inr h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h37 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h38 := h4 h37
            -- One of the premise coincides with the conclusion.
            exact h38
          case inr h39 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h40 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h41 := h4 h40
            -- One of the premise coincides with the conclusion.
            exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208045083159044478831178983566 : (((p5 ∧ (False ∧ p5)) ∨ (p5 ∨ p1)) → (p4 ∨ (p3 ∨ ((((((p2 ∨ (p5 ∧ ((p3 ∧ True) ∧ p4))) → True) → True) → False) → False) ∨ p4)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : (((p2 ∨ (p5 ∧ ((p3 ∧ True) ∧ p4))) → True) → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h12 := h9 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : (((p2 ∨ (p5 ∧ ((p3 ∧ True) ∧ p4))) → True) → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h17 := h14 h15
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117398824117020138503155304568 : ((p1 ∧ ((p1 ∧ (p2 ∧ (p1 ∨ ((p1 ∧ ((p2 → (p1 ∨ (p1 → p3))) ∨ ((False → p5) ∧ (True ∧ p2)))) ∨ p1)))) ∨ False)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136272521817949413878376276195 : ((((True → ((True ∨ p4) ∧ p1)) → p2) → (p2 → (((((p3 ∧ True) ∨ p5) → ((p3 ∧ p5) ∧ p3)) → p2) ∨ p5))) ∨ (True → (p1 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59759658681717935040123717848 : (((p1 ∧ p3) → (p5 ∨ ((((p5 → (p1 ∧ (p2 → (p4 → p3)))) ∨ False) ∧ (((True → p5) → p3) → False)) ∨ ((p1 → True) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634883945030572038125765788221 : (((((p1 ∧ (((((p3 ∧ (((p2 ∧ True) ∨ p1) → (p4 ∧ p2))) → True) → p5) → (p4 ∨ False)) ∨ p5)) ∨ ((p4 ∧ False) ∧ p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357086533945159594581220463091 : (p5 → (((False ∨ p4) → True) → (((True ∧ ((p3 ∧ (p2 ∧ ((p5 → p4) ∧ p2))) ∧ True)) ∨ False) ∨ ((p5 ∨ (p5 ∧ p1)) ∧ (True ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58787904297789128243103912149 : (((p5 → True) ∧ ((p5 ∨ (p1 ∨ (True → ((((False ∧ p4) → False) ∧ (((True ∧ ((False → p4) ∧ p2)) → p4) ∨ p3)) ∧ p4)))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152649068444999769864115764182 : (((True → p5) ∧ (((p1 ∨ (((False ∧ (p4 ∨ (p3 ∨ (p3 → p4)))) ∧ p3) ∧ (True ∧ True))) ∨ p3) → p4)) → (p5 ∨ (p4 ∨ (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4095890709504382206536397764 : (p3 ∨ ((((((p4 ∨ (True ∧ False)) ∨ (p4 ∧ ((((p3 ∨ p3) ∨ p1) ∨ p5) ∨ False))) ∧ (p4 → p3)) ∧ p4) ∨ True) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342145900094245996152440874047 : (p2 → (((p1 ∧ (False ∨ ((((True ∧ p2) ∧ False) ∨ (((p5 → (True ∧ p2)) ∧ p3) ∨ True)) ∧ p2))) ∨ False) ∨ (p3 → ((p5 ∨ p2) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678518238001377077780004240068 : ((((((True ∨ False) ∧ p4) ∨ (True ∧ ((p5 → (((True → p2) → ((p4 ∧ True) → False)) ∧ p1)) → p3))) ∨ (p1 ∧ (p5 → (p3 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649439133187393955980223568506 : ((((((p4 → ((True ∧ (p3 → ((p1 ∨ (p4 → p2)) ∨ (p5 → ((False ∨ False) ∨ p4))))) ∧ p4)) → p1) ∧ (p3 ∧ p5)) ∧ (p2 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61534099766616126522501039313 : ((p1 ∧ ((((((True → True) → (p3 ∧ (p3 ∧ p4))) ∧ p2) ∨ p5) ∨ p5) ∧ ((((p5 ∨ (False ∧ (p3 ∧ p1))) ∧ p3) ∧ p1) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622399451675662990216414590140 : ((((p3 ∧ (((False ∧ p1) ∨ (False ∧ (((p1 → False) → p5) ∧ p2))) ∨ (p2 ∨ ((p2 ∧ ((p4 → p4) ∨ p5)) → (p2 ∧ False))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45570936700233609747480862449 : (((p2 ∨ (p3 ∧ ((((p2 → True) ∧ p4) ∧ True) ∧ ((((p2 ∨ ((p2 ∧ False) → p5)) ∧ True) → p2) ∧ (True ∨ (p3 → p4)))))) → p2) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h7.left
    let h13 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : ((p2 ∨ ((p2 ∧ False) → p5)) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- False on the left can always be used.
        apply False.elim h18
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h19 := h12 h15
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h21 : ((p2 ∨ ((p2 ∧ False) → p5)) ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- False on the left can always be used.
        apply False.elim h24
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h25 := h12 h21
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238773901147617143547588535848 : ((p1 ∨ True) ∧ (p2 → ((p4 → p1) → ((p4 ∨ (True → ((p2 → p4) → (p5 ∨ p1)))) → (((True → p1) → False) → ((p1 ∨ False) → p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (True → p1) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (True → p1) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172459606702397065849763239601 : (((p5 ∧ ((p5 ∧ p4) ∨ p5)) ∨ (False ∧ (p2 ∧ (p5 → (p1 ∧ (p3 ∨ p1)))))) ∨ ((False ∧ (p5 ∨ p3)) → ((p4 ∨ (p3 → p1)) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51657572894279683558468772902 : (((((((p4 → ((p5 ∨ (p1 ∨ p4)) ∨ p3)) → p3) → (p3 ∧ False)) → False) → False) ∧ ((((True ∨ p3) ∧ p4) ∨ False) ∧ (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48376397721348328121258304284 : (((True → (((True → ((p5 ∧ (True ∧ p2)) ∨ p4)) → (((p5 → ((p4 → (p2 ∧ False)) ∧ p1)) ∧ p3) ∨ p1)) ∧ p3)) → (p1 ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138374847812632789983598320198 : ((p4 → (((False ∧ (p4 ∨ p4)) ∧ p1) ∨ ((p1 ∨ p3) → ((p1 ∧ ((False ∨ p4) → (p2 ∨ p1))) ∨ (p4 → p3))))) ∨ (p3 → (p5 ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62943075154571703035228795826 : ((p4 ∧ (p4 ∧ ((((p4 ∨ (p1 → ((p3 → False) ∨ (False ∨ (p1 → (p5 ∧ p3)))))) ∨ p4) → p1) → ((p3 ∧ (p5 ∨ p3)) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186655406741484586015527512592 : ((((True ∨ ((p1 → p4) ∨ p3)) ∨ p1) ∧ (p2 → (p3 ∧ p3))) → (p4 ∨ ((p3 → True) ∨ ((p4 → (((p1 → True) → p1) ∧ p1)) → True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328121508187706818339382200419 : (True → ((((((True ∨ p3) ∨ (p3 ∧ p2)) ∧ p5) ∨ (True → p3)) ∧ ((False ∧ False) ∨ ((p4 ∨ p3) ∧ (p3 ∨ False)))) ∨ (False ∨ (p5 → True)))) := by
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
theorem thm_5_vars_718024950614468999131311570028 : ((((((False ∧ p1) ∨ p5) ∨ p2) ∨ (((True → p2) ∧ ((p4 ∨ (p3 → ((p1 → ((False ∧ p2) → False)) ∨ (p2 → p5)))) → p4)) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316869660387629848716520850437 : (p3 ∨ (p1 → (((False ∧ (((p1 ∧ (p2 ∨ True)) ∧ (p5 ∨ True)) ∨ (False ∨ (False → True)))) ∨ (False ∨ p4)) ∨ ((p3 ∧ (True ∧ False)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167115178530448011979574611019 : ((((((p3 → p5) → (p4 ∧ (False ∧ p1))) → (True ∧ p5)) ∨ (p1 ∧ (p4 ∧ False))) ∨ p3) → ((p1 ∧ ((p3 → p1) → (p4 → p2))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136298760150650666324018593708 : (((p1 → (p1 → ((p1 ∧ False) ∧ p5))) → ((p3 ∧ ((((False ∨ p3) ∨ ((True → p1) ∨ p4)) ∧ p1) ∧ p3)) ∨ p3)) ∨ (p3 ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147511028867019716913577291171 : (((p3 ∨ (((((False → p5) → (False ∨ (p1 → p5))) ∧ ((p3 ∨ p3) ∧ True)) ∨ (True ∧ p1)) ∨ p2)) ∨ p2) ∨ (p4 → (p4 ∨ (False ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149648578822323285020988559148 : ((p4 ∧ ((p5 ∨ (((False → p2) ∧ p2) ∧ (False ∨ False))) ∨ ((((p1 ∧ (True ∨ False)) ∧ p3) ∧ False) ∧ p1))) ∨ (p5 → (True ∨ (p5 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744246771548796531169011271666 : ((((p1 ∧ p3) → (((((((p5 ∨ p1) ∨ False) ∧ p2) ∨ (True ∧ ((False ∨ ((False ∨ p2) ∨ True)) ∨ p2))) ∧ p1) ∧ (True ∧ True)) ∧ p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49650584059884366512587638690 : ((((False ∨ (p5 ∧ (True ∧ p2))) → (((False ∧ (True → (True ∨ (((p4 → p5) ∨ True) ∨ p1)))) → p2) ∧ p4)) → ((p4 ∧ p4) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53525584489287076317390106007 : (((p3 → (((p3 → p5) ∨ ((True ∨ (False ∧ p2)) → p1)) → True)) → (p2 → (((((p1 ∨ p5) ∨ False) ∧ (p2 → p4)) ∧ p1) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215281769271813689771892296127 : ((False ∧ (p5 → (p4 ∧ p3))) ∨ (((p4 ∧ (p1 ∨ (((p5 → p3) ∨ p4) ∨ (False → ((True ∨ p3) ∧ True))))) ∨ p3) → (p3 ∨ (True ∧ p4)))) := by
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
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45852614584011605132973335104 : (((p2 → (p1 → ((p5 ∧ (p4 ∨ ((p3 ∧ (True ∧ p2)) ∧ ((((p4 ∧ (False → p2)) ∧ (p3 → p3)) → p3) ∨ False)))) → p3))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308497945167900663775818768732 : (p2 ∨ (((((p2 → (((p5 ∨ (p5 → ((p3 ∨ p5) ∨ p3))) ∧ (p1 → p4)) → True)) ∧ p4) → p1) ∧ (p5 → ((True → p4) → False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776640762561857497774556452009 : (((p1 ∨ ((p1 → (p3 ∧ (p1 ∧ ((((p3 → (((p2 → p5) ∨ False) → p3)) ∨ True) → True) → ((p1 ∧ p1) ∧ (p3 → p4)))))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_181210739928488311351838864019 : ((p2 ∧ ((False ∨ (p4 ∨ p2)) → (p5 ∧ (p4 ∨ ((p3 ∧ p2) ∨ p3))))) → (p1 → ((p2 → p4) → ((p5 ∧ (p3 → (p3 → True))) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353838928609661708212097772471 : (p4 → (p1 → ((p3 ∧ (((((p2 → (p3 ∨ (p3 → (p5 ∨ p5)))) ∧ p2) ∧ True) ∨ (p1 ∧ p1)) ∨ (((p5 → p1) → p2) → False))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158200180662338337047120744004 : ((((p5 → p3) ∧ p2) ∧ (True → (True ∧ (((p3 ∧ (p4 → False)) → ((True ∧ p2) → p5)) → p5)))) ∨ ((False ∧ p3) ∨ (False → (p1 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_339624472542309841115069500662 : (p1 → (p2 ∨ ((p4 → ((p5 → (p5 → (p2 ∧ (p2 ∧ ((p2 ∧ True) → True))))) ∨ p2)) → (((True ∧ ((p5 ∧ p4) ∨ p2)) → False) ∨ p1)))) := by
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
theorem thm_5_vars_740124391326700267361686071244 : ((((False ∨ p3) ∨ (((p1 ∨ (True ∨ p4)) ∨ (False ∧ ((((p3 ∨ False) → True) ∨ ((p3 → p4) → (p2 ∧ p2))) ∨ p4))) ∧ (p2 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134391231193505694098872792978 : (((p5 ∨ (p2 ∨ ((p2 ∧ ((True ∨ p5) → (p3 ∧ ((p2 → ((True ∨ False) ∧ p1)) → (p4 → True))))) ∨ False))) ∨ p4) ∨ ((True → False) → p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258785437553786773854209911069 : ((True → False) → ((((p5 ∨ False) ∨ ((p2 ∨ p5) ∧ p3)) ∧ (p4 ∨ ((p3 ∨ False) ∨ True))) → (p4 ∨ ((p4 ∨ (p2 ∨ p5)) → (p2 → p3))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h11 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h12 := h1 h11
            -- False on the left can always be used.
            apply False.elim h12
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h15 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h16 := h1 h15
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h22
      case inr h23 =>
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h26 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h27 := h1 h26
            -- False on the left can always be used.
            apply False.elim h27
          case inr h28 =>
            -- False on the left can always be used.
            apply False.elim h28
        case inr h29 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h31 := h1 h30
          -- False on the left can always be used.
          apply False.elim h31
    case inr h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h33 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h37 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h38 := h1 h37
            -- False on the left can always be used.
            apply False.elim h38
          case inr h39 =>
            -- False on the left can always be used.
            apply False.elim h39
        case inr h40 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h41 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h42 := h1 h41
          -- False on the left can always be used.
          apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354615580460964470476218595420 : (p5 → ((((p3 ∨ ((((True ∧ (p2 → (False ∧ p1))) ∨ p5) → p3) → False)) ∧ (((p3 ∨ (p5 → False)) ∧ p1) ∧ (p3 ∧ True))) ∨ p5) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37407531544259340312780947841 : ((((((((False ∨ ((((False ∧ p3) → True) ∧ p1) ∨ p3)) → (p5 ∨ p5)) ∨ ((p3 ∨ True) ∨ p3)) → False) ∨ (True → p2)) ∨ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342566681486631941446384575795 : (p2 → (((((p3 → (p4 ∧ ((p5 ∧ p1) ∧ p4))) ∧ p3) ∨ p2) → p5) ∨ (((False ∧ ((p4 ∧ p1) → (p5 ∨ (p1 ∧ p1)))) ∧ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227923462694885427278531433521 : ((p3 ∧ (True ∧ True)) ∨ (False ∨ ((((((p1 ∨ p1) ∨ (False ∨ p3)) ∨ p1) ∨ p3) ∨ p2) ∨ (p2 ∨ (((False → p3) ∨ False) ∧ (True ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321390141777362792745758358246 : (p4 ∨ (True → (True ∧ ((p2 → (((p1 ∨ True) ∨ (p2 → (True → (p4 ∧ p4)))) → ((p3 → False) ∨ ((p5 ∧ p5) → (True ∨ p3))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113461234077826177279426695660 : (((((p2 ∨ ((p1 ∨ p3) ∧ ((p5 ∨ p4) → (p5 ∨ p4)))) → (True ∧ ((p1 ∨ p3) ∧ (False ∨ p1)))) → p5) ∨ (p3 ∨ p2)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350926407051711287385394863939 : (p4 → (((((((p3 → p4) ∨ (p3 ∨ p5)) ∧ (((p1 ∧ p3) → (p5 ∨ p4)) ∨ p3)) ∧ (True → (p3 ∧ p2))) ∨ p5) → p1) ∨ (False ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318629924726791922034935959689 : (p4 ∨ ((p1 ∧ ((((((True ∨ p4) → (((p5 ∨ (True ∧ (True → p5))) ∨ (p3 ∧ p4)) ∨ p3)) ∧ False) ∨ p3) ∧ True) ∨ True)) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46065601862249559514643756023 : ((((((((p3 ∨ (p1 → True)) ∨ ((p3 ∨ (((False ∧ p3) → (True → True)) → p3)) ∨ p4)) ∧ p1) ∨ p4) → False) ∨ p3) ∧ (p1 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117610164937421324965961973690 : ((p2 ∧ (p2 → ((((False → (p3 ∧ p5)) ∧ p1) ∧ (False → p4)) ∨ ((p1 ∧ ((p5 ∨ p3) ∨ p2)) ∨ ((True ∧ p5) → p1))))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118141313677471639730203649733 : ((False ∨ (((p1 → (False ∨ p1)) → (((p4 → (p2 ∧ p3)) → (p1 ∧ p5)) → p2)) ∨ (p1 ∨ (((p4 ∧ p2) → p2) ∧ p2)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958260641510502299339181820463 : ((((p2 → (p5 → p2)) → ((p1 ∧ (p1 → ((False → (p4 ∨ ((p3 ∨ True) → p1))) → ((p3 ∨ p1) ∧ (p4 ∨ (False ∨ False)))))) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p5 → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186693694511691127946387016815 : (((((True ∨ p4) → (p5 ∨ p2)) ∧ p2) ∨ (False → (p5 ∨ p5))) → (((False ∨ ((True ∧ p2) ∧ ((p5 ∨ True) → (p4 ∨ p4)))) → p4) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h17 : (p5 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h17
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48518105766793923860550624457 : (((((p3 ∨ (((True ∨ p2) ∧ False) → (False → p3))) ∧ ((True → ((p1 ∨ p3) ∨ (True ∨ False))) ∧ p3)) ∨ p1) ∧ ((p1 → p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42149376519465425648465238986 : ((((False → False) → ((((p4 ∧ p2) ∨ ((p1 → (True → (((p4 → False) → p5) ∧ p2))) → ((p1 → True) ∨ True))) → p2) ∨ True)) ∨ p3) ∨ p4) := by
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
theorem thm_5_vars_68915094024161444267600622244 : ((p4 → (p1 ∨ ((True ∨ (((p4 → (True ∨ (p5 ∨ (p4 ∧ ((False ∧ ((p3 → True) → p5)) ∨ False))))) ∧ (True ∧ p3)) ∨ p1)) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4127647304963519197229551238 : (p3 ∨ (False ∨ ((p4 ∨ (((((p1 ∧ (p3 ∧ p4)) ∧ p1) ∨ (p3 ∨ p1)) ∨ (p1 ∨ True)) ∧ ((p3 → True) ∨ (True ∨ p5)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



