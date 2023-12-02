variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199643662880760901419499209580 : (((((p2 ∧ True) ∨ p2) → (p4 ∨ p2)) → False) → (p3 ∧ (True → ((p4 → False) ∧ (False ∧ ((p1 → ((p5 ∧ (p2 ∧ p3)) ∧ False)) ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ True) ∨ p2) → (p4 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((p2 ∧ True) ∨ p2) → (p4 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h17 := h1 h11
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (((p2 ∧ True) ∨ p2) → (p4 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h23
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h24 := h1 h18
  -- False on the left can always be used.
  apply False.elim h24
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h25 : (((p2 ∧ True) ∨ p2) → (p4 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h26
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h30
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h31 := h1 h25
  -- False on the left can always be used.
  apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257416623710619558111681306846 : ((p2 ∨ p5) → (p1 → ((((((True ∧ (True ∨ p1)) ∧ ((False ∧ p3) ∨ True)) ∨ (p5 ∧ (False ∨ ((True ∨ False) → True)))) ∧ p1) → p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329031184766428188771344217967 : (True → (((True ∨ p4) ∧ (p5 ∧ (p2 ∧ p2))) → ((((p4 ∧ (p1 ∧ (((((p4 → True) ∨ p1) ∨ True) → p3) ∧ p2))) ∧ False) ∨ p3) ∨ p2))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669762327260098556145702987709 : ((((((p1 → (False ∧ p2)) ∨ ((p1 ∨ (p1 ∧ (p4 ∨ p1))) ∨ (p1 → p1))) ∨ ((p4 ∨ p3) → (False ∧ True))) ∨ ((True ∧ False) → True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_245135869108641224789283117168 : ((p2 ∧ True) ∨ ((False → p2) → (((False → p3) ∧ (((((p3 ∧ p1) ∧ p3) ∧ False) ∧ ((p4 ∧ ((False ∨ p5) → p3)) → p5)) ∧ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301278681117339264322619253094 : (False ∨ (((((p3 → p2) ∧ True) ∨ p5) ∨ p3) → ((True ∧ (((False ∧ p4) ∨ (p3 → (p4 → ((p1 → False) → True)))) ∨ p1)) ∨ (p5 → False)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
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
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h13 =>
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
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Implications on the right can always be decomposed.
    intro h16
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215829131938648278320822931561 : ((p2 ∨ ((p3 ∨ p4) ∨ False)) ∨ ((p3 ∧ p2) ∨ (((p2 ∨ (True → (p2 ∧ (p5 ∨ ((p1 ∨ p2) ∨ p1))))) ∧ ((p5 ∧ p1) ∧ p5)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98947434291946547793789125145 : ((True → (((p3 ∧ (p2 ∨ (p5 ∧ p2))) ∧ (((p2 ∧ ((p1 ∧ False) ∧ p2)) ∧ (True ∨ (p2 → p5))) ∧ p2)) ∧ ((p3 → True) ∧ p3))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10623623702893480467148109135 : (((p5 → ((p4 ∨ p2) ∨ (p3 → (p2 ∨ ((p3 → p2) → (((((p3 ∧ True) ∧ (p1 ∧ (False ∨ False))) → True) ∨ True) → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624750204288357194681515779653 : ((((p5 ∨ (((((p2 ∨ (((p2 → p3) → p5) ∧ p5)) ∧ (p2 ∨ p3)) → (p4 ∧ ((p3 ∨ p4) ∧ p2))) → (p2 ∧ p5)) ∧ p2)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_246009591282776240790375975330 : ((p4 ∧ False) ∨ ((((((p4 ∧ True) → ((((p5 ∧ p4) ∧ p1) ∨ True) ∧ False)) → (((p4 ∨ (False ∨ p3)) ∨ p4) → p3)) ∨ False) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127621349834760117399638438870 : ((p5 ∨ (((p1 → (p5 ∧ ((((p1 ∨ False) ∨ (p3 → p3)) ∨ p2) ∧ (p2 → False)))) ∧ (p2 ∧ ((p2 → p3) → False))) ∨ p5)) → (p1 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h11 := h6 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171693351261215223338494257501 : (((True → ((True ∨ p1) → (((p5 → p5) → (False ∨ p4)) ∨ (p4 ∨ p3)))) ∨ p1) ∨ (True ∨ (((p4 ∨ False) ∧ p1) → ((p1 → False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111166374480672023040528013425 : (((((True → True) → (p2 ∨ p2)) ∧ ((p5 ∨ p2) ∧ (p4 → (((True ∧ p5) → ((p3 ∨ (p2 ∨ p4)) ∨ False)) ∨ p5)))) ∧ p5) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342472045351281295424319672377 : (p2 → (((((p5 ∧ p5) ∧ (True → ((p2 ∧ p5) → p5))) ∧ (p1 ∨ False)) ∧ False) ∨ ((True ∨ p2) → ((p2 ∧ p1) → (p1 → (p1 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353655375541581054324960345592 : (p4 → (p5 ∨ (((((True ∨ True) ∧ (True ∧ p1)) ∧ p1) ∧ (p4 ∧ (((p4 → p4) ∨ (p5 ∧ (p4 ∧ p2))) → ((p4 → p3) ∧ p1)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180096366465165456546023369712 : ((((True ∧ (((p4 ∧ True) → True) ∧ ((p5 ∨ p5) ∧ p1))) ∧ p1) → p2) → ((((p1 ∨ (p3 ∧ ((True ∨ False) → p5))) ∧ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776071173416135483227677260162 : (((False ∨ (p5 → (((p1 → ((p4 ∨ p2) ∧ (((p5 → (p1 → True)) → p4) → True))) ∧ (False ∨ ((p5 ∧ (p2 ∨ False)) ∨ p1))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336576042799246405091614837017 : (p1 → ((((False ∨ (((((True → True) ∧ False) ∨ (((p4 → (p5 ∨ p1)) ∧ (False ∧ p5)) ∧ p5)) ∧ p4) ∧ (p4 ∨ p5))) ∨ p1) → False) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ (((((True → True) ∧ False) ∨ (((p4 → (p5 ∨ p1)) ∧ (False ∧ p5)) ∧ p5)) ∧ p4) ∧ (p4 ∨ p5))) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52926221042323345526189578786 : ((((((((p4 ∨ p5) ∨ p2) → False) ∨ True) ∧ (False ∧ p5)) ∧ p3) ∧ ((p3 → False) ∨ ((p1 ∨ ((p1 → (False → p5)) ∧ p3)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317650773735296950584513246715 : (p4 ∨ (((p3 → (((p2 ∨ p2) → p1) ∨ ((((p4 → (p1 → p5)) ∨ p2) ∧ (p5 → (False ∧ (p3 ∧ p1)))) → (p1 ∨ p3)))) ∨ p4) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701249442140523618412777351337 : ((((((p4 ∨ p2) ∨ (False ∨ (p2 ∨ p3))) ∨ (p5 → p5)) ∧ (False → (p1 ∧ (((((p5 → False) ∧ p2) ∨ True) ∨ (p5 → p2)) → p3)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h2
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184137060911117556170232781144 : (((p4 ∧ ((((p2 → (True → True)) → p5) ∨ False) ∧ p4)) ∨ True) ∨ ((((((p3 ∧ False) ∨ (p1 ∨ p3)) ∨ True) → (p4 ∨ True)) ∨ p5) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225767961664069995357860997179 : (((p5 → False) ∧ p4) ∨ ((p1 ∨ ((True ∧ p1) ∧ (False ∧ (p2 ∧ p3)))) → ((((False ∧ ((False ∧ True) ∧ (p3 ∧ p2))) ∧ p4) ∧ p1) ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138195959049485491701538230061 : ((p1 → (p2 ∨ (p4 ∧ ((True ∨ p4) ∧ (((((p4 ∧ p1) ∧ (p4 ∧ (p1 ∧ (p3 → p1)))) ∧ p1) ∨ False) ∨ p5))))) ∨ ((False → p4) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175717049901926049696276827864 : ((((p1 → True) → (p3 → (p5 → ((p2 ∨ (True ∨ p1)) ∨ p5)))) ∧ True) ∧ (((p5 ∧ p5) ∧ (p2 → (p1 ∨ p4))) ∨ (True ∨ (p2 ∧ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_14695346864171062370406534717 : (((((p2 ∧ ((p5 ∨ ((p4 ∧ p2) ∧ ((p2 ∧ True) ∨ ((False ∨ (p1 → p2)) ∧ p5)))) ∨ p2)) ∨ True) ∨ (p1 ∨ p3)) ∨ (p1 ∨ p4)) ∧ True) := by
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
theorem thm_5_vars_207075149411147196676613984249 : (((p3 ∧ (True → (p2 ∨ True))) ∧ p2) → ((((p2 ∧ (((True ∧ (True → False)) → p4) → (((p5 → p2) ∧ False) ∧ True))) ∨ True) ∨ True) ∧ p3)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65624422812024660606232048552 : ((p4 ∨ ((((((p3 ∨ False) ∧ (p2 ∨ ((((p2 ∨ ((p5 ∨ p4) ∨ p2)) ∧ True) → False) ∧ p3))) ∧ (p2 ∧ True)) ∧ p3) ∨ p1) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231855867700266199075911419465 : (((p5 ∧ p5) → p2) → ((((p4 ∨ p5) → (((p4 ∨ False) ∧ ((p3 ∨ p1) ∨ (p3 → (p1 ∧ p5)))) ∨ True)) ∨ ((False → True) ∨ p1)) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41990613299825250790461907539 : ((((p5 ∨ p5) ∧ (((True ∧ p5) → False) ∨ (((False → (True ∧ (((p1 → (p2 ∧ True)) → p2) → (p3 ∨ p1)))) → p2) ∨ p3))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174949390584964255406050000989 : ((True ∧ ((p4 ∨ (p1 ∨ (p3 ∧ ((True → (p3 ∧ (p5 ∨ p2))) ∧ p1)))) ∧ p4)) → (((((p5 ∨ False) ∨ p4) ∧ (True ∨ True)) ∨ p2) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320527070707051975229494786426 : (p4 ∨ (True ∧ ((p2 ∨ ((p4 ∨ (((p5 ∧ True) → True) → False)) ∧ False)) ∨ ((p3 ∧ ((((p5 ∨ p1) ∧ p3) → p3) ∧ (p5 → False))) ∨ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114297796326795569642454308267 : (((((((p5 ∧ (p3 ∧ p5)) ∨ (p1 → (True ∨ p2))) ∨ p3) → p1) ∧ ((p4 ∧ p4) → p1)) ∧ (((p1 ∨ p5) ∨ p3) ∨ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46612132475377307640615730266 : (((p2 ∧ (p4 → ((((False ∨ (p2 ∨ p4)) ∧ True) ∧ ((p2 ∧ p4) ∨ ((p1 ∧ (p3 ∧ p1)) ∨ (p2 ∨ False)))) ∧ False))) ∧ (p5 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193338005171813935350578322326 : ((((p3 ∧ True) ∨ False) → (p4 ∨ ((p1 → False) ∧ p4))) → (((p3 ∨ True) ∧ ((((p3 → p3) → p2) ∧ ((False ∨ False) → True)) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686554390054097706290757131097 : (((((p1 ∨ p1) ∧ ((p4 ∧ (True → (p1 → ((p4 → (p4 ∧ (p5 → False))) ∨ False)))) ∧ True)) → (((p2 → (p2 → p3)) ∨ p2) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160259858084248649304298974318 : (((p5 ∧ ((False → p5) → (((((p3 ∨ False) ∧ False) ∧ p1) ∨ (p4 ∨ p3)) ∧ p4))) ∨ (p3 ∨ p1)) → ((p5 → p3) ∨ (p4 ∨ (p3 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157510945005927200888480478298 : (((p4 ∧ (((True ∨ p2) ∧ ((p3 → p5) ∧ (p3 ∨ (p1 ∧ (p1 ∨ p1))))) ∧ True)) ∨ (p3 ∧ True)) ∨ (p1 → ((p4 ∧ (p4 → p5)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56228678834570929064394622257 : (((p4 ∨ ((p4 ∧ p3) ∧ p4)) ∨ (p4 ∨ (((((True → False) ∧ False) ∨ p5) ∧ True) ∨ (((False → p2) ∨ (p4 → p2)) ∨ (p4 → p5))))) ∨ False) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138377058654474516901276656808 : ((p4 → ((p1 ∨ (p3 ∨ p5)) ∧ (((p4 → (((p5 ∨ False) ∨ (p5 ∧ ((p2 ∧ p1) ∨ p2))) ∨ p2)) ∧ p5) ∧ False))) ∨ ((p5 ∧ False) → p4)) := by
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
theorem thm_5_vars_678670752998752390292127081489 : (((((p4 ∧ p4) ∨ ((True ∧ (True → (p3 → ((False ∧ p4) → ((p4 → False) ∧ (p2 → p4)))))) → False)) ∨ ((p4 → p5) → (p4 → p5))) ∨ False) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113022756606803481433851582227 : (((True ∨ (((False ∧ ((((p3 ∨ p4) ∧ ((p5 ∧ p4) → (p5 ∧ p1))) → (True ∧ p1)) → p4)) → (p5 ∨ False)) ∨ p5)) → p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259357171747972486383029217586 : ((False → p2) → (p4 ∨ ((True → (p4 ∧ p4)) ∨ (p2 → ((True ∨ p3) ∧ ((p5 ∨ (True ∧ (((p3 ∧ p5) ∧ p3) ∧ p3))) → (p2 ∧ True))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707667716301306077897829258632 : (((((p2 ∨ p5) ∨ ((p4 → p2) ∨ (p3 ∨ p1))) ∨ (True ∨ (((p1 ∧ p4) ∨ (((True ∧ (p1 ∧ p2)) → False) → (True → True))) → p2))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_303730299232701099180886830926 : (p1 ∨ ((((p3 → p2) ∧ ((p5 → (p4 ∨ ((p4 ∧ ((p1 ∧ (True → ((p1 → True) ∧ True))) ∧ p1)) ∧ (p5 ∧ p1)))) ∧ p2)) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231877416121640465581133934084 : (((True ∨ p2) → False) → (p2 → ((False ∨ ((p2 → p2) ∧ p2)) → (((p3 ∨ (p3 ∨ p4)) ∨ ((p5 → (p5 ∧ p4)) ∨ (p4 ∨ p2))) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (True ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60462488411305054193498653918 : (((p5 → p2) → (p4 ∨ (((p3 → True) ∧ (p5 ∧ p2)) → ((p1 ∨ ((p5 ∨ (False → (p5 ∧ ((p2 → p1) → p4)))) ∨ p3)) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310398164582650701125814547468 : (p2 ∨ (((p5 ∧ p4) ∧ (((p1 → False) ∧ p3) → True)) ∨ ((p3 → True) → (((False ∧ p2) ∨ (p1 → p1)) ∧ (p3 ∨ (True ∨ (p4 → p4))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258885706205910808551413534445 : ((True → p2) → ((((((p4 ∨ ((p4 ∨ p5) → True)) ∨ (p5 ∨ ((p4 ∨ (p5 ∨ p1)) ∨ p3))) ∧ p1) ∧ p5) ∧ ((True → p1) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247406654665624638914637745318 : ((False ∨ p2) ∨ ((((False ∨ p1) ∨ (((p1 ∨ (p1 ∨ (p1 → True))) → p4) → (((p3 → p2) ∨ (p4 → (p5 → True))) ∨ p2))) ∨ p4) ∨ p4)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694176254035287949973978159012 : (((((((p4 → (p3 ∧ False)) ∧ False) → p2) → (p3 → ((p3 ∧ p2) ∧ p1))) ∨ ((p5 ∨ (False → (p2 ∨ (False ∨ p2)))) → (p5 ∨ True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113736788802815999561652979085 : (((((((p1 ∨ p4) ∧ p2) → (p2 → (((p1 ∧ p4) ∧ p3) ∨ p2))) → p3) ∨ (p1 ∧ (p5 ∨ (p2 ∧ p2)))) → (p1 ∨ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39451393045520945583891073270 : (((p5 ∧ (((((p2 ∧ p2) ∧ (p2 ∧ p5)) ∧ p3) ∧ True) ∧ ((p3 ∨ ((p1 ∧ p1) ∧ (p1 ∧ ((p4 ∧ False) ∨ False)))) → p4))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55438684759423294499034743641 : (((((True → (False ∨ p4)) ∨ p4) → p5) → ((((p3 → p4) → False) ∧ ((p4 ∨ p4) → p3)) → (p2 ∧ (p5 ∨ ((p4 ∨ True) ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60879959929767298073589738667 : ((True ∧ (p1 → ((((p4 ∧ (p2 ∨ (False → p1))) ∧ p2) → False) → ((p3 → p3) → ((False ∧ p2) ∨ ((p4 → (p4 ∧ p2)) ∨ p1)))))) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207866441397970432379889220469 : ((((True → False) ∨ p2) ∧ (p4 ∨ p2)) → (((p5 ∧ (False ∨ ((((False ∨ (p5 ∨ (p5 → True))) ∧ p3) → p4) ∨ (False ∧ p5)))) ∨ p5) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h7 := h4 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753731668572081944594595474204 : (((False ∧ (((p2 ∧ ((((p1 → p3) ∧ p3) ∨ p3) → False)) ∨ (p5 ∧ True)) ∧ ((((p5 ∧ p3) → p2) ∨ (p3 → True)) → (p5 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115333463166451288017554726402 : (((p4 ∧ (((p4 ∨ (p5 ∧ (p4 ∨ p2))) ∨ p1) → True)) → (False ∧ ((p3 ∧ (p5 ∧ ((True ∧ True) ∧ p3))) → (p1 ∨ False)))) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199604753813575572234693033633 : ((((False ∧ ((p4 ∨ True) → p3)) → True) → False) → (p3 → (((p5 ∨ p1) → (((p2 ∨ (True ∧ (False ∧ (p1 ∧ p5)))) ∨ p5) ∧ p3)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ ((p4 ∨ True) → p3)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589546680604082474309569054627 : ((((((((p5 ∧ (p2 ∨ p1)) ∨ (((((p4 ∨ p3) → (p5 ∨ p2)) ∨ ((p3 ∨ p1) ∨ p1)) → True) ∧ False)) → p4) → p3) → p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48685629466012412389562235917 : ((((((True → p3) → (p1 ∨ (p5 ∧ True))) → p2) ∧ ((p1 ∧ (((p3 → p2) ∨ (p3 ∧ False)) ∧ False)) ∧ False)) ∧ (p3 ∨ (True ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204564796896120155903134658264 : ((((p4 ∧ False) ∧ (p3 ∧ p4)) ∨ p1) ∨ ((False → p3) ∨ (p5 ∧ ((((p2 ∧ p5) ∨ (p5 ∨ (p4 → (p3 ∨ p3)))) ∧ (p2 ∧ p5)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620221642316919841928737433909 : (((((p4 ∧ p2) ∨ (p2 ∧ ((p3 ∧ p3) → (False ∧ (p4 → ((False ∧ (p5 → ((False ∨ p3) → (p5 ∧ (p2 ∨ p1))))) ∧ p4)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672559256425920084919279837738 : (((((((((p4 ∧ (False ∧ p5)) ∧ p1) ∧ (False → (p4 ∧ p2))) → (False ∨ p5)) ∨ (p4 → False)) ∧ (True → False)) → ((p5 ∨ p5) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129151227186458784022922728277 : (((((p1 → ((p1 ∨ p2) ∧ p1)) → ((p3 ∧ (p5 ∧ (p2 → ((p1 ∧ True) ∨ p1)))) ∨ p5)) ∧ (p3 ∧ p1)) ∨ True) ∧ (p3 → (p1 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259133376297367831763181723041 : ((False → True) → ((((p5 → ((((p3 → p1) → ((((p5 ∧ True) → p3) ∨ (p4 ∧ p2)) ∨ p5)) ∨ p1) → (False ∨ p5))) ∨ p3) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 → ((((p3 → p1) → ((((p5 ∧ True) → p3) ∨ (p4 ∧ p2)) ∨ p5)) ∨ p1) → (False ∨ p5))) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h3
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47467593432855859227452769643 : (((p5 ∧ (((True ∧ p2) ∨ p3) ∧ ((True → ((p3 ∨ False) ∧ ((p1 → p4) ∨ (((p4 → p1) ∨ p5) ∧ p5)))) ∨ True))) ∨ (True ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152209093326642828957785713337 : ((((((True ∧ False) → p3) ∧ p5) → p1) ∧ (((((p3 ∧ (p1 ∨ (p4 ∧ p1))) ∨ p2) → p2) ∧ p4) ∨ p4)) → (p3 ∨ (p2 ∨ (False ∨ p4)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153107811413444735464639804177 : ((p4 ∧ (((False ∧ (p2 → (((p1 ∧ p2) → p2) ∨ p2))) ∨ ((True ∨ p2) ∨ (p5 → (p3 → False)))) → p3)) → (p1 ∨ ((p2 ∨ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ (p2 → (((p1 ∧ p2) → p2) ∨ p2))) ∨ ((True ∨ p2) ∨ (p5 → (p3 → False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_511215075924789926007923055535 : ((((p5 → p5) ∧ (False ∨ ((p3 ∧ ((p4 ∧ (((p3 ∨ (p5 → p3)) ∨ p5) ∨ True)) ∧ (p1 ∨ ((p3 ∨ p3) ∧ True)))) → (p1 ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
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
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h26 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h33 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h37 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67326922311879968917566128562 : ((p1 → (((((p5 ∨ p2) ∧ True) ∧ ((False ∨ (p5 → (False ∧ ((True ∨ p3) → (p3 ∨ (p3 ∨ (p5 ∧ p1))))))) ∨ p1)) ∨ p1) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350918859494146380590491368696 : (p4 → ((((((((False → p5) → True) ∧ (p1 → p3)) → (p1 ∧ p2)) ∧ p2) ∧ ((((False ∧ p3) → False) ∨ True) ∧ p1)) ∨ True) ∨ (p3 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134431533427805967872577564844 : (((p5 → (((((((p2 → p4) ∨ (p2 ∧ False)) → (p5 → p2)) ∧ p5) ∨ p2) ∨ (p5 → p2)) ∨ (True ∨ p2))) ∨ p1) ∨ ((p4 → p2) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351426279246912805230355294850 : (p4 → ((p5 ∨ ((p5 → p2) ∨ ((p1 ∨ (False ∧ p3)) ∧ ((p2 → False) ∧ (p4 ∧ (True ∨ (True ∨ p5))))))) ∨ ((p1 → (p2 ∨ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134066238981773307700258161037 : ((((((p1 ∧ ((False ∧ p3) → (p5 ∧ (p5 ∨ p3)))) ∨ ((True ∧ p2) ∨ (p3 ∧ (True → p1)))) ∨ p5) → p2) ∨ p1) ∨ (True ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160515184853688882565373087849 : (((False → ((p1 ∧ p4) ∧ (False ∨ ((True ∨ p4) → (p4 ∨ False))))) ∧ ((p2 ∧ (p5 ∨ p4)) ∧ p2)) → (p1 ∨ (p2 ∨ (p2 ∨ (p3 ∧ p2))))) := by
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
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711781454394477348305639810658 : (((((((False ∧ p5) → p3) → p1) ∧ p4) ∨ ((((p1 → (p3 → (p4 ∨ (p1 ∨ (p5 → (p1 ∨ p2)))))) → p5) → False) ∨ (True ∨ p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181403980788796862920549161895 : ((p2 ∨ ((p5 ∨ ((True ∧ True) → ((True → (True ∨ p3)) ∧ p1))) ∨ True)) → (((p3 ∧ p3) ∨ (p5 ∧ p4)) → ((p5 → p3) → (p3 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h11 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h22 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h21
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h23 := h3 h22
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h25 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h26 := h3 h25
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h26
      case inr h27 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h29 := h3 h28
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350111273792903364091740431469 : (p4 → ((((((p5 ∨ p5) ∧ p5) → (p2 → p5)) → ((p4 → (p5 → ((p1 → p3) → p2))) ∨ True)) ∨ (p3 ∨ (p2 → (p1 → p5)))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154490181480516663205861781801 : (((((p3 ∨ ((False ∧ p4) ∧ (p2 ∧ p2))) → False) ∧ (((p4 ∧ p3) ∧ p4) ∧ (p4 ∨ p1))) → p2) ∧ (p1 → (((p5 ∧ p2) ∧ p4) ∨ p1))) := by
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
  cases h5
  case inl h10 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h11 : (p3 ∨ ((False ∧ p4) ∧ (p2 ∧ p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (p3 ∨ ((False ∧ p4) ∧ (p2 ∧ p2))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261042507532487259215814445984 : ((p4 → p2) → ((p2 ∨ (False ∧ p2)) → (((((p2 ∨ (p4 → (True ∧ p3))) ∧ p5) → p5) ∨ p3) → (p3 ∨ (((p4 ∧ False) ∧ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165809689965454293061047531497 : ((((p2 ∨ p4) → p2) ∧ (p3 → (((((False → False) → (True ∧ p5)) ∧ p4) ∨ p3) ∨ False))) ∨ (p5 ∨ ((p2 ∧ p3) ∨ ((False → p5) ∨ p3)))) := by
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
theorem thm_5_vars_309314780349305878055462940827 : (p2 ∨ (((p1 ∧ ((p1 ∨ (p5 ∨ ((((p3 → False) ∧ p3) ∧ p4) ∧ ((p3 → (True ∨ p1)) ∧ p5)))) ∧ (p5 ∨ p5))) ∨ p4) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264182933133224251150105719744 : (True ∧ (((((p4 → (p2 → True)) ∨ True) → False) ∧ p2) → ((((((p4 ∨ p1) ∧ p5) ∨ (p4 → (True ∧ (p3 ∨ p5)))) ∧ p2) ∨ True) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_620156492385147637339358939567 : (((((p2 ∧ True) ∨ ((((((p3 ∧ (True → (p4 ∧ True))) ∧ True) ∨ True) ∨ (p3 ∧ ((False ∨ True) ∨ p1))) → (p2 → False)) ∧ p3)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207552315646914433681457688945 : (((((p1 → p5) ∧ p5) ∨ True) → False) → ((p3 ∧ ((((p4 ∧ (p2 ∨ p1)) ∨ (True ∨ p3)) ∧ p1) ∧ p5)) ∧ (((p5 → False) → False) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → p5) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 → p5) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 → p5) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p1 → p5) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (((p1 → p5) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307117749752447805645625977665 : (p1 ∨ (False ∨ ((True → ((((True ∧ (True → p4)) ∧ ((p4 → p1) ∨ p5)) ∨ True) ∨ (p1 ∧ ((p1 → p4) ∨ ((p4 ∧ p4) → True))))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307210727583032207950102668464 : (p1 ∨ (p1 ∨ (((p2 ∧ p3) ∧ p1) ∨ (True ∨ (p2 ∨ ((p4 ∨ p2) ∧ ((p3 ∧ ((p5 → True) ∨ (((False ∨ p4) → False) → True))) ∧ p1))))))) := by
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
theorem thm_5_vars_68652842135531778859477225035 : ((p4 → (((True ∧ ((p4 → True) ∨ ((((p3 ∧ p2) ∧ False) ∨ (p2 ∨ (False → False))) → False))) → (True ∧ ((p4 ∧ False) → False))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167483706909593141371684258038 : ((((((((p4 ∧ (p3 ∧ False)) → p4) → (p2 → p3)) ∨ p5) ∧ p1) ∨ p5) ∧ (p4 → p5)) → (p3 ∨ ((False ∨ (p4 ∨ p1)) ∨ (True → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721212035976274090037273775074 : (((((p4 ∧ True) → (True ∧ False)) → (((p4 ∨ ((p4 ∧ (((p2 ∨ True) → p4) ∧ ((False ∨ True) ∧ (p4 → p1)))) → True)) → False) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_56380356243038074091993845291 : (((((p3 ∧ True) ∨ p3) → False) → (((False ∨ (((p2 ∧ p1) ∨ p1) ∨ (p3 ∧ True))) ∧ p5) ∨ ((((p5 → p3) → p3) → p4) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209421077485467829871649080282 : ((p2 → ((p3 → (p2 ∧ False)) ∨ p1)) → (((p5 ∨ (p4 ∨ ((((p3 ∨ p4) ∧ (p4 → True)) → p2) ∨ p2))) ∨ (False ∨ (True ∨ p2))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185062543126670772787167168040 : (((p2 ∧ p1) ∨ (((p5 ∧ p4) ∨ (p1 ∧ p1)) → (p5 ∧ p2))) ∨ ((p5 → (((p2 ∨ True) ∧ p3) → p1)) ∨ ((p5 → (p5 ∨ p3)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349222987126648432038774723778 : (p3 → (p1 → (((((p4 → True) ∧ True) → (((True ∧ (p5 → p3)) ∧ (((True → True) ∨ (p5 → p4)) → p2)) ∧ False)) ∨ True) ∧ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117228307608567310401163384586 : ((True ∧ ((p5 → p4) → ((p4 ∧ p3) ∧ (((p4 ∨ ((((True ∧ (p4 ∨ False)) → p3) → p2) → True)) ∧ p3) → (True → False))))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150549567907409493440727399532 : (((((p5 → (p2 ∧ p5)) → (p3 ∧ False)) → ((p1 ∨ p5) ∧ ((p2 ∧ p5) → ((True → p5) ∧ True)))) ∧ p5) → (((p4 → p3) ∨ True) ∨ p3)) := by
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
theorem thm_5_vars_253727024219655485372987710107 : ((p1 ∧ p1) → ((p2 → ((((p2 → False) → p5) → (p3 ∨ (True ∧ p4))) ∧ ((p1 ∧ False) ∧ ((p3 → ((True ∨ p2) → True)) ∨ False)))) ∨ True)) := by
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
theorem thm_5_vars_358060429511147430150121786124 : (p5 → (p1 ∨ ((((p5 ∨ True) → (p1 → p5)) ∧ p4) ∨ (p4 ∨ ((False ∨ False) ∨ ((p1 ∧ p5) ∨ (p5 → (p1 → (True ∧ (True ∨ p5)))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



