variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114687292144177401340814113423 : (((True → ((((p5 ∧ False) ∨ (p1 ∧ p4)) ∧ p3) ∧ ((True ∨ (p4 → p3)) ∨ p3))) ∨ (p3 ∨ (p1 ∨ ((True ∨ p3) ∧ False)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171448349670923959879764414175 : (((p2 ∧ ((((p5 ∧ (True → (p3 → (p1 ∨ False)))) → p1) ∨ p1) ∧ p5)) ∧ True) ∨ (((((p1 ∧ p2) ∨ p5) ∨ p1) → (p1 ∨ p5)) ∧ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133745271844441615884792109345 : ((((p2 → ((((p2 → False) ∨ p4) ∧ p3) ∨ p1)) ∧ ((p3 ∧ ((True ∨ (p3 ∨ p5)) ∧ (False ∨ p3))) ∧ p5)) ∧ p2) ∨ (p1 → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44293190430008252041057292663 : (((((False → ((p2 ∧ False) ∧ False)) ∧ (((False → ((True ∨ True) → p4)) ∧ p2) → p5)) ∧ (((p2 ∧ p5) → (p1 → p3)) → p5)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112829916875967128315712130736 : ((((p5 ∧ (p2 ∧ (p3 ∨ p2))) ∨ (p1 → ((((p2 ∧ p3) ∧ (p2 ∨ True)) ∨ ((False → p4) ∧ (p4 ∨ p4))) ∨ p4))) → p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233871556295573101557745446283 : ((p4 ∨ (True ∨ p5)) → (((((True → p2) → p1) → (p1 ∧ (p2 ∨ False))) ∧ (p5 ∨ (p5 ∨ ((p3 ∧ p5) ∧ False)))) ∨ ((p4 → p4) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135142988890970736563597789286 : (((p3 ∨ ((True → (True → (((p4 → p4) ∧ (p3 ∨ False)) ∧ (((p2 → p3) → False) ∧ p3)))) → p2)) ∨ (False ∨ p1)) ∨ ((p4 → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160181501704312001108113870283 : (((p3 ∧ ((((((p5 ∨ ((p2 → p5) → p3)) ∧ False) → p1) → False) → p3) → p2)) ∧ (p1 → p3)) → ((p4 ∧ ((True → False) ∧ False)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((((p5 ∨ ((p2 → p5) → p3)) ∧ False) → p1) → False) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90895202301153203300432745110 : (((p5 ∨ p2) ∧ (True → ((p3 → ((p4 → (p1 → False)) ∨ ((p1 ∧ ((((True ∨ p1) → p2) ∨ p4) ∨ p1)) ∨ (p3 ∧ p4)))) ∧ False))) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648711700058741734384403096152 : (((((False ∧ ((True ∧ (((True ∨ ((False ∨ False) ∧ (p4 ∨ ((p5 ∨ (p4 ∧ True)) → p5)))) ∨ p5) ∧ p3)) ∨ p3)) ∨ p2) ∧ (p4 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112971772746158675869663466890 : (((p1 ∧ (((((p1 ∧ True) ∧ (True ∨ True)) → p2) → p3) ∧ ((((False ∨ False) ∧ p1) → p2) → (p1 ∨ (p2 ∨ p5))))) → p5) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61649935881631223391818285831 : ((p1 ∧ (p1 ∧ ((p4 ∧ ((((p3 → p3) ∧ (p4 ∨ (p5 → ((((p5 → p3) → (False ∨ p4)) ∨ p5) ∨ p4)))) → p2) → True)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320437678819384527535320687053 : (p4 ∨ ((p2 ∨ p3) → (((p3 → (((p4 ∨ p1) ∧ (p1 ∨ p3)) → False)) → p3) ∨ (((p5 → (p3 ∧ p5)) ∧ (p1 ∧ (p2 ∧ False))) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53875412114711167358939594393 : ((((p1 ∨ p1) ∨ ((((True → p1) ∨ p5) → p1) ∧ False)) ∨ ((((False → p2) → (p4 → ((p4 ∨ p5) → p1))) → True) ∨ (p3 ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114069835626235856904433514160 : (((((p1 ∨ ((p4 ∨ False) ∨ p3)) ∨ False) ∨ ((p1 ∧ (((p3 ∧ False) ∧ (p3 ∧ p5)) ∧ p3)) → True)) ∨ (False ∨ (False ∧ p1))) ∨ (p2 ∨ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206478069648572593764919070994 : ((p5 ∨ (((p5 → p3) → True) ∧ False)) ∨ (p3 → ((((((p1 ∨ (False ∧ (p1 → False))) ∨ (True → False)) → p5) ∨ (p1 ∨ p3)) → p4) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∨ (False ∧ (p1 → False))) ∨ (True → False)) → p5) ∨ (p1 ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166009142026673621540762007334 : (((p1 ∨ False) ∨ ((p2 → (p5 → (((p2 ∧ p3) → ((p4 ∧ False) ∧ p2)) → p1))) ∧ p2)) ∨ (((p3 ∧ p1) → False) ∨ (p3 → (p4 ∨ True)))) := by
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
theorem thm_5_vars_336330431074966070868110735428 : (p1 → (((p1 ∧ (p2 ∧ p5)) ∨ ((False ∨ p4) ∨ (p4 ∨ (p2 ∨ ((((False ∨ p2) ∧ (True ∧ (p4 → (p3 ∧ p4)))) → p5) ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_751817324957664861447706531769 : (((True ∧ (False ∨ (p1 ∧ (True → (((p3 → p1) ∨ (p1 ∧ p1)) → ((((p2 → p5) → p1) → p2) ∨ (p3 ∧ (p5 ∧ (True ∨ p5))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69101865645077845798543312646 : ((p5 → (((((p4 ∨ (p1 ∧ p4)) → p5) → (p2 ∨ (p1 → ((p5 → (p5 ∧ p2)) ∧ ((p4 ∧ p3) → p2))))) ∨ p5) ∧ (p5 ∨ p1))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599074901410441613762864015904 : (((((True → False) ∧ (((p4 ∧ p3) → p5) → ((True → ((((True ∧ p3) → ((False → p1) → p3)) → (p1 ∨ p4)) ∨ p3)) → p3))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141895148456436620707683155272 : (((p3 → p3) ∨ ((p4 → p3) → ((False → (p4 → (((p3 ∧ (p4 ∧ (p3 ∨ p3))) → False) ∧ p1))) ∨ (p4 ∧ p4)))) → (p2 → (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213433864939165802041659177358 : (((p4 ∨ (p3 ∧ p4)) ∧ p3) ∨ ((p4 ∧ (p3 ∧ p2)) → (((((True → (p2 ∧ p3)) ∧ ((p4 ∧ p3) → False)) ∧ p4) ∨ (p4 → True)) ∨ p1))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158964605347932467193068686471 : ((p2 ∨ (p5 → (((p1 ∧ (p1 ∧ (p5 → p5))) ∧ (p3 ∧ False)) ∨ ((p4 → p1) ∧ (p3 ∧ True))))) ∨ (True ∨ ((p3 ∨ (False ∧ True)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_12553307846063871577473236531 : ((((p5 → (p2 ∨ p5)) → ((p4 → ((p1 → ((((p1 ∧ (p1 ∨ True)) ∧ (p5 → p2)) ∧ (False ∧ False)) → True)) ∧ p5)) ∧ False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 → (p2 ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351421704796197416647531056181 : (p4 → ((p5 ∧ ((p2 ∧ ((True ∨ (False ∧ False)) ∧ (p1 ∨ True))) ∨ ((True ∧ p3) ∨ ((p4 ∧ False) ∨ p1)))) ∨ (True ∨ (p1 ∧ (True ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48589769548638268783304896886 : ((((((p4 → ((p2 ∨ (True ∨ p1)) → p5)) ∨ p3) ∨ ((p2 ∨ False) ∧ (p5 → (p1 ∧ True)))) ∧ (True ∨ True)) ∧ ((True ∧ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64718952922226648911020160522 : ((p1 ∨ (p3 → (p1 ∨ (((p1 ∧ p3) ∨ (p2 ∨ ((p1 ∨ (p1 ∧ p5)) ∧ (True ∨ (p5 ∨ p5))))) ∨ ((True ∧ p4) ∨ (True ∨ p4)))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_591442969180572090374681448007 : ((((((p4 → p2) ∨ ((p2 ∧ ((((p5 ∨ p5) → p3) ∧ (False → True)) → p2)) ∨ (p5 ∨ ((p3 → False) ∨ p2)))) ∧ (p2 ∨ p1)) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112381038232978657164031999196 : (((((((p2 ∨ (p1 ∧ p3)) ∨ (p5 → (p4 → p1))) ∧ (p4 ∨ (p3 ∨ p5))) ∧ ((p1 ∧ (p5 ∨ True)) → p2)) ∧ True) → p5) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117561103724593524414562037909 : ((p2 ∧ (((p1 → ((True → p1) ∧ p2)) ∨ p2) ∧ ((p5 → (False ∨ (p3 → ((True ∧ (False ∨ p4)) ∨ (False ∨ p4))))) ∨ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255528633307527791689005361708 : ((p5 ∧ p2) → (p1 ∨ (((((p4 ∧ ((p4 → p3) → (((p3 → p5) ∧ p1) ∨ p3))) → p2) ∧ p2) ∧ p2) → (((p2 ∨ True) → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800316830822378883743673452810 : (((p2 → (((p5 → ((p5 ∨ (False → p5)) → ((p1 ∨ (p3 ∧ p2)) → p1))) ∧ ((p1 ∨ (((False → p4) → p3) ∧ p2)) ∨ p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59638368166490248227518051182 : (((p5 → p3) ∨ ((p1 ∨ (((p1 ∨ p2) → ((p5 ∨ p1) ∨ (((p3 → (p3 ∧ p4)) ∧ (p4 ∨ p5)) ∨ False))) ∨ True)) ∨ (p2 → True))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_319281555038350152938686773208 : (p4 ∨ (((p5 ∨ True) ∧ (p1 → (p5 ∨ (((True → p3) ∧ ((p2 ∨ p1) → p4)) ∧ p3)))) ∨ ((False → ((p2 → p3) → (p4 ∧ p4))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321406017617232325071550903359 : (p4 ∨ (True → (p4 → (p1 → (True → ((((p2 → (p4 ∨ ((False ∧ p4) → p3))) → False) ∨ p1) ∨ (p4 ∧ (p3 ∧ (p5 → (p4 ∧ p5)))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168830102408787891554558159497 : ((p3 ∨ (((((p5 ∧ p5) ∨ (p1 → p5)) ∧ p3) ∨ ((p3 ∨ (p3 → p1)) ∨ p1)) ∨ p1)) → ((False ∨ ((False ∨ p4) ∨ (True ∧ True))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Conjunctions on the right can always be decomposed.
            apply And.intro
            -- True on the right can always be proven directly.
            apply True.intro
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62498910169921668525992245462 : ((p3 ∧ (p1 ∧ ((((p2 ∧ ((p4 ∧ ((True ∧ (False → (True ∧ p3))) ∧ p2)) ∨ p5)) ∧ p3) ∨ (p2 ∧ (p5 → (p2 ∧ p3)))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47218086754866775194817591966 : ((((((p5 → p1) ∧ (((True → False) ∨ p2) → p5)) → True) → ((((p4 ∧ (True → p1)) ∧ (True ∨ p5)) ∨ p4) ∧ p2)) ∨ (p1 ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47531238169300575328008714113 : (((p4 ∨ (((((p2 ∨ p5) ∨ p3) ∧ (True → ((p3 ∧ (False ∧ p2)) ∨ (p5 ∨ p1)))) → p2) ∧ (p2 ∨ (p4 ∨ p4)))) ∨ (p2 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232479090087985118385988861776 : ((True ∧ (p4 ∨ False)) → (p2 → (((p3 ∨ False) ∨ False) ∨ ((p4 ∧ p5) ∨ (((p3 → (((p1 ∧ (p4 ∧ p5)) ∨ p4) ∨ p5)) ∨ False) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64399654717070114840364639834 : ((p1 ∨ ((((((((p5 → (p3 → p2)) ∨ p1) → p4) ∨ (True ∨ p5)) ∧ p2) → (True → (p4 → p1))) ∨ ((p4 → p3) ∧ False)) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341733033291130461136491154510 : (p2 → (((p2 ∧ p2) ∧ ((((False ∨ ((True ∨ p2) → p1)) → ((p3 ∨ (p3 ∨ p1)) → (p3 ∨ False))) ∨ p1) ∨ (p3 ∧ p4))) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714174120169139368739649105233 : (((((False → ((p1 ∨ p3) ∧ p3)) → p4) → (((p2 ∧ ((p1 ∧ p5) ∧ p5)) ∧ ((p1 ∨ True) → (True → (True ∧ (p5 ∧ False))))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49881491972076409472546245304 : (((((p4 ∨ (p4 → ((((p5 → p2) ∨ (True → p4)) ∧ (p2 ∨ (p3 ∧ p5))) → p2))) → p3) ∨ True) ∧ ((False ∧ True) → (p4 → p4))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323507986737136245950908713501 : (p5 ∨ (((p4 → (p5 ∨ p1)) ∨ ((False ∨ p2) ∨ ((p2 ∨ p4) → (((p2 ∧ False) ∨ p5) → ((p3 → True) → p3))))) ∨ (p1 ∨ (False ∨ True)))) := by
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
theorem thm_5_vars_218383479064508991051321273661 : (((p5 → p1) ∨ (p4 ∧ p3)) → (((p1 ∧ (p5 → p3)) → ((p1 → ((p1 ∧ p5) ∧ (False → ((p5 → (p3 ∧ False)) ∨ True)))) → p1)) ∨ p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136356986155459181131476318548 : (((((p2 → p5) ∧ p1) ∧ p5) ∨ (((((False ∧ p3) ∨ p3) ∧ p2) ∨ (p1 → p4)) ∨ ((False ∧ (False ∧ p5)) ∨ True))) ∨ ((True ∧ p5) ∨ False)) := by
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
theorem thm_5_vars_266058696892850643183101234356 : (True ∧ (p2 → ((((p3 → (p3 ∧ (p3 ∧ (p5 ∨ (p5 ∧ p5))))) ∧ (True → (True ∧ (p1 → ((False → (p2 → p5)) ∨ p4))))) → p4) ∨ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67350372080036795086906372286 : ((p1 → ((False ∧ (True ∨ (p3 ∧ (p5 ∧ (((False ∨ (p4 ∧ p2)) ∧ False) ∧ ((p3 ∨ ((p4 ∧ p2) → p1)) ∧ (False → True))))))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230505463342130357126819929380 : (((True → p3) ∧ p1) → (((p5 → False) ∨ (((((p5 ∧ (((p1 → ((True ∨ p2) ∧ False)) ∨ p1) ∧ p1)) → p2) ∧ p3) → p5) ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233078817775802167967171335469 : ((p4 ∧ (p5 ∨ p5)) → (((False ∨ (p3 ∧ p5)) → (p4 ∧ (p2 ∧ False))) → (((True ∧ (p2 ∧ ((p5 ∨ p2) → p3))) ∧ p4) → (p1 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h13 : (p5 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h14 := h9 h13
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h16 : (p5 ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h17 := h9 h16
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160830130754449236305706715596 : (((False ∧ ((p1 ∧ (p2 ∧ False)) ∨ True)) → (((p2 ∨ True) → ((p5 ∧ (p3 ∨ p2)) → False)) ∧ p2)) → (p5 ∨ ((True → False) ∨ (False → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166435318914358451198615323572 : ((p1 ∨ (True → ((False → (p5 → False)) ∧ ((p2 ∨ ((p3 ∨ p2) ∨ p4)) → (p4 ∨ p1))))) ∨ (((p5 ∧ (False ∨ (p1 ∧ True))) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206487136717576523717456875821 : ((p5 ∨ ((p3 → (p5 → p4)) ∨ p3)) ∨ ((p3 ∧ (False ∨ p1)) ∨ (False → ((p2 ∨ (p1 ∨ p2)) ∧ (((p3 ∧ (False → p4)) → p4) → p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318842634353057720688453648530 : (p4 ∨ ((p4 → ((((p3 ∧ False) ∧ p4) → p2) → ((((True → p2) → p4) → False) → (p5 ∨ ((False → p3) → p3))))) ∧ ((p3 ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True → p2) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198085328215000822667567518313 : (((p4 ∨ p5) ∨ ((p2 ∧ p1) ∧ (p5 ∧ p4))) ∨ ((p3 ∧ (p3 → (((True ∧ p3) → p1) ∧ (p4 → ((p5 ∧ True) ∧ p5))))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160969692613314264364715867867 : (((p5 ∧ (p4 → p3)) ∧ (((((p4 ∧ True) → p4) → (p3 → p3)) → p2) → ((p3 ∧ False) → p4))) → (p1 → (((p3 ∧ p3) ∨ p2) ∨ p1))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598728462348397658235649881351 : (((((True ∧ p4) ∧ (((False → (False ∨ True)) → ((p2 ∨ p2) ∨ (p3 ∨ ((False → ((p1 → True) → True)) ∧ p5)))) ∨ (p5 → p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86088814697852815587878114380 : (((False → (p5 ∨ ((False ∧ (False → p3)) ∨ (False ∨ p3)))) ∧ ((True → p5) ∧ (((((True → p3) → p4) ∨ p1) ∧ False) → (True ∨ p1)))) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690474697013064982034988256754 : (((((((p5 ∨ ((p1 ∧ p4) ∧ p1)) → p5) → (((True → p2) → p2) ∧ p4)) ∧ p1) → ((((True ∧ p5) → p2) ∨ (False ∧ True)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61148831019966496500049447952 : ((False ∧ (((p1 ∧ p1) ∧ (p3 ∨ False)) ∧ ((False ∧ ((False ∨ (p4 ∧ ((p3 ∨ (True ∧ p2)) ∨ ((True → p2) → p5)))) ∨ p5)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111687550441226753434821188389 : (((((((False ∨ (((p5 ∧ p5) ∧ p4) ∨ p4)) ∨ p1) ∧ ((p4 ∧ (p5 ∨ (p4 ∨ (p2 ∧ p2)))) → p1)) ∨ p5) → False) ∨ p3) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116534009735692161462422908353 : (((True ∨ p4) ∧ ((((((((True → p3) ∨ ((p5 ∧ p4) → p1)) ∨ p5) → False) ∧ ((p4 ∧ False) ∨ p5)) ∨ p4) ∨ p4) ∧ p1)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40444896898847302538435637445 : ((((((((p2 ∧ True) ∨ p5) ∧ p2) ∧ False) ∧ ((p2 → (p5 ∧ (True → (p1 → ((p4 → (False ∧ p3)) ∧ p5))))) ∧ p3)) ∨ p5) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57762048079989263224835073427 : ((((p4 → False) → False) → ((p2 ∧ p1) ∨ (((((p3 ∧ (True ∨ p4)) → False) ∨ ((True ∨ (p1 → p1)) → True)) → p3) ∨ (True ∨ p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_700843588376670446073287687367 : (((((p1 → ((((p1 ∧ True) ∧ False) ∧ False) ∨ p1)) ∧ True) ∧ (((p4 → True) ∨ ((p1 → p5) ∧ p2)) → ((p3 ∨ p5) ∧ (False ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149266058080514282359089014538 : (((p5 ∨ p4) ∨ (p2 ∧ (((p2 → ((False ∧ p5) → p4)) → ((p4 ∧ p1) ∨ (True ∧ p2))) ∧ (p2 → p2)))) ∨ (p3 ∨ ((p5 → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231531911320069919020094744264 : (((p4 → p3) ∨ p4) → (p1 ∨ ((p1 → p3) ∨ (((p3 ∧ p1) ∨ (p5 ∨ p3)) ∨ (((False ∧ False) ∨ (((p3 ∨ p3) ∧ False) ∧ p5)) → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h13 =>
        -- False on the left can always be used.
        apply False.elim h11
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h22 := h20.left
      let h23 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h25 =>
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111571792553717435432433606834 : (((((p1 ∧ p1) ∧ ((((True → (((False ∨ p4) → p4) ∧ (p1 ∨ False))) → p2) ∨ (p2 ∨ False)) ∨ (p3 ∨ p1))) ∧ p1) ∨ True) ∨ (p2 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53361485629602039078285697118 : (((((p1 → (True → p5)) ∨ (p4 → (p2 ∨ (p1 ∨ True)))) ∨ p5) → ((p4 ∧ (p2 ∧ ((False → ((True ∨ p3) ∧ p3)) → p2))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67294363813701538398994125471 : ((p1 → ((((p5 ∨ (p2 ∧ (True → True))) ∨ (((p1 → False) → (p5 ∧ True)) → ((p4 → (p1 → p2)) ∧ p4))) ∨ (p3 ∧ p5)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84501015571383551885077332152 : (((((p5 ∧ p4) ∧ ((p5 ∧ (p4 ∨ (p1 → p1))) → (False → p5))) ∨ (True ∨ p5)) → ((p3 → (p1 ∧ ((p2 ∨ p2) → p4))) ∧ False)) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p4) ∧ ((p5 ∧ (p4 ∨ (p1 → p1))) → (False → p5))) ∨ (True ∨ p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_216238717706390599634592220294 : ((p1 → ((False → False) → False)) ∨ ((p3 ∨ ((p2 ∨ (p1 → p1)) ∧ (p1 → ((p1 ∨ p3) → p4)))) ∨ (p1 ∨ ((p1 ∨ (False ∨ p3)) → True)))) := by
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
theorem thm_5_vars_47292431709415908947566854563 : (((((p1 ∧ p5) ∧ True) ∧ ((p2 ∧ ((False ∨ False) ∧ (p2 ∨ ((True → p2) ∨ ((p1 ∧ p3) ∨ (p5 ∧ True)))))) ∧ p4)) ∨ (p3 → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39840955272086625455319465406 : (((p1 → (((((p4 → ((p3 ∨ p2) ∨ p4)) ∨ (p1 → p3)) ∧ p3) ∨ ((p2 ∨ p5) ∧ p4)) ∧ (p4 ∧ (p5 ∨ (p3 → p2))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181096334929646956930485521571 : (((p2 → p4) → (p3 → (False → (p2 ∨ ((p2 → (p2 → p4)) ∧ p5))))) → (((p5 → (p4 ∨ p1)) ∨ (p5 ∨ (p4 → (p1 → p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38735615989835317567848530774 : ((((p4 ∨ ((p2 → (p1 ∨ p1)) ∨ p1)) → ((((p3 → p2) ∧ p5) ∨ (((p1 ∧ p2) → p1) → (p3 ∧ (p5 ∨ True)))) → p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192577104210659303453161926908 : (((True → ((((p1 ∨ p1) ∧ True) ∧ p5) ∧ True)) ∨ False) → ((((((p3 ∧ (p2 ∨ ((p1 → p4) ∧ p3))) ∨ False) → p4) → p1) ∨ p3) ∨ True)) := by
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
theorem thm_5_vars_262487740442981820664446052476 : (True ∧ ((True → (p1 → (((((False → False) ∧ True) ∧ (((p4 ∧ p3) → False) → (p2 ∧ (p1 ∨ True)))) ∧ (p1 ∨ (p4 ∨ p2))) ∨ p4))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307770583906769538913430220741 : (p1 ∨ (p3 → (False ∨ ((True → ((False ∨ ((p3 ∨ p2) ∨ p2)) ∧ ((p3 ∧ p1) ∨ p5))) ∨ ((False ∨ (p3 ∨ (p4 ∧ (False → p2)))) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338513805182666430505766853924 : (p1 → (((p1 ∧ False) ∨ p4) ∨ (p4 ∨ (p4 → (p2 ∨ ((True ∧ (p3 ∨ ((p2 ∨ (True ∨ p3)) ∧ ((p5 → p3) → p4)))) ∨ (p4 ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115878706299781313805376232725 : ((((p1 ∨ (p4 ∨ False)) ∧ p2) ∨ (p1 → ((p1 ∨ (True → (p1 → ((False → p5) ∨ False)))) ∧ (((p3 ∨ p5) ∨ False) ∨ p1)))) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230575445475145350619917959947 : (((p1 → p1) ∧ p4) → ((p2 → ((False ∧ ((True ∧ p3) → p2)) ∨ ((((p4 ∨ ((True ∧ True) → p2)) → p1) ∨ p5) ∧ (True → p1)))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112280724271926124783076151235 : (((True → (p5 ∧ ((((True ∧ (((True ∨ (p2 → p1)) → p2) ∧ (p5 → p4))) ∧ (False ∧ p3)) → (True → p3)) → p1))) ∨ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311971772983083622506568355001 : (p2 ∨ (p3 ∨ (p4 ∨ (((p4 ∨ p1) ∨ (p3 ∨ ((True → True) ∨ p3))) ∨ (p5 → ((((p2 → (True ∨ p5)) ∧ (p3 ∧ p2)) ∧ p4) ∧ p4)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68321285879402202325356362013 : ((p3 → ((True ∧ ((p2 ∨ (((False ∧ ((p4 ∨ p5) ∧ p5)) ∨ True) ∧ p4)) ∨ (p3 ∨ False))) ∨ (False ∧ ((p4 ∨ p2) ∨ (p1 ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658540812228745964745104721732 : ((((p2 ∨ ((True → (p4 ∧ ((p1 ∨ p4) ∨ p2))) ∧ (((p1 ∨ True) → (p3 ∧ p5)) → (p1 ∧ ((p5 → p3) ∨ False))))) ∨ (p5 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113849300784362769311790569430 : (((True → (((True → False) ∨ (((p3 ∧ (p4 → p3)) ∨ ((p5 ∨ p1) → (p2 ∨ False))) → p3)) → (False ∧ True))) → (p3 ∧ p5)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190960289867520773880027995940 : (((p4 ∨ (p3 → (p3 ∨ p2))) ∧ ((p5 → p4) ∧ p5)) ∨ (p4 → (((False → p5) → False) ∨ ((p4 ∨ False) ∨ ((p1 → (p2 → p5)) ∨ True))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166222869850281022142254244535 : ((p2 ∧ (((True ∨ (p5 ∧ (False ∨ ((p2 ∨ p3) ∨ p4)))) → (p5 ∧ p2)) → (p5 ∧ False))) ∨ (((True ∧ True) ∨ ((p5 → False) ∧ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724674778675120378706057012801 : ((((p2 ∨ (p2 ∨ p3)) ∧ ((((False ∨ False) ∧ p4) ∨ (p5 ∨ p2)) ∧ (False ∧ (p1 → (p2 ∨ (((p2 ∨ p4) → p2) → (False ∨ p4))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241655986571314791152604341342 : ((False → p5) ∧ ((((p2 ∨ p5) ∧ (p2 ∨ (p5 → ((False ∧ (p2 ∧ p5)) ∧ p5)))) ∨ ((p3 ∨ False) → True)) ∨ (((p4 ∨ p1) ∨ True) ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47429616727590390897259917656 : (((p2 ∧ (((p5 → ((True ∨ True) ∨ True)) ∧ ((p4 ∧ ((False ∨ (p1 ∧ p3)) → ((p1 ∧ True) → p2))) → p3)) ∨ False)) ∨ (True ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734820122059027528401959806480 : ((((p2 ∨ p1) ∧ (((p3 ∧ (p2 ∨ p1)) ∧ (p4 ∧ p4)) ∧ (p4 → (((p5 ∨ p4) ∧ ((p1 → (p3 → p2)) ∧ p3)) → (p1 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41142064397561088031355615569 : (((((((p4 ∧ (p2 → ((p5 ∧ p5) ∨ p2))) ∧ (False ∨ p2)) ∧ p3) ∨ (((p2 ∨ p2) → p5) ∨ p5)) ∨ ((p3 → True) ∨ False)) ∨ p3) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734355333360790688616298585286 : ((((False ∨ p3) ∧ (True ∧ (p1 ∨ (p5 ∨ (p5 ∨ ((((p5 ∧ True) ∧ True) → p5) → (p2 ∨ (p3 ∧ (p2 ∨ (True → (False ∧ p5))))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748630112556084549644626791473 : ((((p3 → p2) → ((False ∨ (((True ∧ p4) → p1) ∧ ((p5 ∨ p1) ∨ ((p1 ∧ False) ∨ ((p4 ∨ p1) ∨ p4))))) ∨ ((True ∨ p2) → True))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166263002349250793281909149613 : ((p3 ∧ (((p2 ∨ p4) ∧ True) → ((((p3 ∨ p3) ∧ p4) ∧ p5) ∨ (False ∨ (p4 → p1))))) ∨ ((((p4 → p3) ∧ False) ∧ (p4 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322482989495452179020335196012 : (p5 ∨ (((p2 ∧ False) ∨ (((p3 → (((True ∨ ((p2 ∧ p5) → p2)) ∨ (p4 → p2)) → (p3 → p4))) ∧ (p4 ∧ (p5 ∨ p5))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



