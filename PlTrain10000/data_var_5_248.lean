variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190254849876449978866790296319 : ((((p5 ∨ ((p1 ∧ p1) ∧ (p1 ∧ p2))) ∧ p3) ∨ p1) ∨ ((False ∧ False) → (p1 ∨ (((((p2 ∧ p4) → True) ∨ (p2 ∨ p1)) ∧ p3) → True)))) := by
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
theorem thm_5_vars_47066140236988151146493202556 : ((((((False → False) ∧ False) ∨ ((p1 → p3) ∨ ((((False ∧ (p3 ∧ p3)) ∨ p1) ∨ (p1 ∨ p2)) ∧ p5))) ∨ (True ∨ p1)) ∨ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119607954888782786885057895009 : ((p5 → (p3 ∨ (((p2 → False) → ((True ∨ p1) ∧ ((p4 ∨ p4) ∧ ((p3 ∧ (p5 → p3)) ∧ True)))) ∧ (p3 → (p5 → p3))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603754046686572314123662771280 : ((((p4 ∨ (((p5 → (((p4 → p3) ∧ (False ∧ True)) ∧ (p4 ∨ True))) ∧ (p5 ∧ (p5 ∧ p5))) → (p2 ∧ ((p5 ∧ p4) ∧ p1)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301055553402369432263724523039 : (False ∨ (((p5 ∨ (False ∨ (p4 ∧ True))) ∨ ((p2 ∧ p5) → p3)) ∨ ((((False → ((p4 → ((p4 ∧ p1) ∧ p1)) ∧ True)) ∨ p1) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137949190750985684552310701129 : ((p5 ∨ ((((False ∧ ((p5 ∧ (p3 → (p5 ∧ (False → p3)))) ∧ p1)) ∧ (p3 → False)) ∨ (False → (p4 → p3))) ∨ p3)) ∨ ((p2 ∧ p4) → p4)) := by
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
theorem thm_5_vars_187508621486893613700351323885 : ((p1 ∨ (((p2 → p4) → ((p2 ∧ False) ∧ (p2 ∧ p1))) ∨ False)) → (p3 ∨ (((False ∨ (True ∧ (False ∨ p1))) → ((p3 ∨ p4) → p2)) ∨ True))) := by
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
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158539285988462025559131286062 : (((p1 → p5) → (p1 → (p3 ∧ ((False → (True ∨ True)) ∧ ((True → (False ∨ p2)) → (p4 ∧ p4)))))) ∨ (True ∨ ((p5 → p2) ∨ (p4 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86341630946126645565305383755 : (((((p2 ∧ (p2 ∧ (p1 ∨ (p3 → False)))) ∨ True) ∨ False) → (p4 ∨ (p1 ∧ (p1 → ((((p4 → (True → p2)) → p4) → p2) ∧ p4))))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ (p2 ∧ (p1 ∨ (p3 → False)))) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205384710620127712873636881932 : ((((p2 → p5) ∨ False) → (p5 ∨ p1)) ∨ (p1 → (((True → p2) ∨ p1) ∨ (p2 → (((p4 → ((p2 ∧ p2) → (p2 ∨ p3))) ∨ True) ∧ p4))))) := by
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
theorem thm_5_vars_111552598341621439214308539205 : (((((p3 ∧ (((p2 ∧ (p3 ∧ (p1 ∧ p3))) → (True ∨ ((p5 ∨ p1) ∨ p4))) ∨ p5)) ∨ ((p5 ∨ p4) ∨ p3)) ∧ p4) ∨ False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215734435985336468571769153866 : ((False ∨ (p5 ∨ (p1 → False))) ∨ (((p4 ∨ (((((p3 → (p2 ∨ p2)) ∧ p1) ∨ p2) ∧ p1) ∧ True)) ∨ p4) ∨ (True ∨ ((p2 ∧ True) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160587569701608911166096638639 : ((((p2 → (p2 → (False ∧ (p3 ∧ (p2 → False))))) ∧ p2) ∧ (True → (((False ∨ p3) ∨ p4) ∨ p2))) → (((p4 ∧ (False ∧ p1)) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193021355772065344858041399264 : ((((True → p1) ∧ ((p5 → p5) ∧ p5)) → (p2 ∧ True)) → (p3 → (((p2 → p3) → ((False ∨ ((p2 ∨ p3) ∧ p5)) ∧ (p5 → p5))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45574302977025302431490078533 : (((p2 ∨ (p2 ∨ (p3 → (p2 ∧ ((((p1 → (False → p4)) ∨ p2) ∧ ((p4 ∧ (False → ((p4 → p4) ∧ p4))) ∧ p2)) → p4))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137065554619855819385399748153 : (((p3 → p2) → (p4 ∧ ((((p4 ∨ p5) → p4) ∧ False) ∨ ((p3 ∧ (p3 ∧ (False ∧ (p4 ∨ (p4 ∧ True))))) ∨ p4)))) ∨ ((False ∧ p3) → p5)) := by
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
theorem thm_5_vars_599272204593269954881233230922 : (((((True ∧ p5) ∨ ((p3 ∨ ((((p5 → (p3 ∨ (p4 ∧ p4))) ∨ (p5 → True)) ∧ (p1 ∨ p4)) → (p3 → p4))) ∨ (False → p3))) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136953231227994168255681425781 : (((True ∧ p2) → (((p4 → (p4 ∨ p5)) ∧ p2) → (((p1 → (p2 → True)) ∧ (((p1 ∨ False) → p3) ∧ p5)) ∧ p5))) ∨ ((p3 ∧ False) → p5)) := by
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
theorem thm_5_vars_708023761965340163737327545339 : ((((p2 ∨ (((True ∧ True) ∧ False) ∨ (p2 ∨ False))) ∨ (((True ∨ p5) → (p2 ∧ p4)) → ((((p2 ∧ p2) ∧ p2) ∧ (p3 ∨ True)) ∧ p2))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161788017230034213212036111747 : ((p5 ∨ ((((p1 ∧ ((False ∧ ((p2 ∨ p4) ∧ (p2 → p4))) → p5)) → False) ∨ (p4 → True)) ∧ p1)) → ((((p3 ∨ p2) → p5) → p5) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133609121168480548140621621323 : (((((p4 ∨ (((p5 ∨ ((False → (p1 ∧ (p2 ∨ False))) ∧ (p2 ∧ (p2 ∧ False)))) ∧ p3) ∧ True)) → p5) → p1) ∧ False) ∨ (False ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192631648039606912496142096006 : ((((((p4 ∧ (p3 ∧ True)) → p5) ∨ p1) ∨ p4) → p2) → ((((p3 → p1) → (p1 ∧ ((p2 → (p1 ∧ (p3 ∨ False))) ∨ p2))) → p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117324483867825193288723110138 : ((False ∧ ((True ∨ ((((False ∧ p1) ∧ False) → p2) → p3)) → (((p4 ∧ (p1 ∧ ((False → p2) ∨ (p1 → p4)))) ∧ True) ∧ p2))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137990911418441671878190147304 : ((p5 ∨ (p2 ∧ (((p5 ∨ (p3 ∨ False)) → (((p5 ∧ p5) ∧ p3) ∨ (p3 ∧ (p5 ∨ (p5 ∧ p5))))) ∧ (p5 ∨ p5)))) ∨ (True ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112669654907519421758009486327 : ((((True → (((((p4 ∨ (p3 ∧ False)) → p2) → ((True ∨ True) → p2)) ∧ (p3 ∨ p2)) → p4)) ∨ ((p4 ∧ p4) ∧ p2)) → p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187751367092548149802724922384 : ((p2 → (((p3 → (p5 ∧ True)) ∨ (p2 → (False ∧ False))) → True)) → (((((True → p5) ∧ True) ∨ (p1 ∨ True)) ∨ p1) ∨ (p2 → (p2 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_61484842837643714583605041258 : ((p1 ∧ ((((p2 → (p2 ∨ False)) ∧ False) ∨ ((((((False ∧ p3) ∨ p5) → True) ∨ False) ∧ (p4 ∨ True)) → p2)) ∧ ((p2 → p4) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305488758416498444138751844587 : (p1 ∨ ((((p4 → False) → (p1 ∨ (p5 ∧ (p3 ∨ ((p1 → p2) ∧ p3))))) ∧ p5) ∨ (p2 → ((p4 → False) → (True ∨ ((True ∧ p4) → p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228807488699725187506597524655 : ((p3 ∨ (p2 ∨ p1)) ∨ ((((False → p3) → p3) ∨ ((p1 ∨ p2) → ((p4 ∧ p2) → ((((False ∨ p2) → p1) → p3) → p2)))) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45464737121012934166051062572 : (((False ∨ ((p4 ∨ (((p1 → (False ∨ p2)) → (p4 → False)) → ((p4 ∧ (False → ((p4 ∨ p1) ∧ p2))) ∨ (p5 → False)))) ∧ p2)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172249928530321189718494183036 : (((p2 ∧ (((p2 ∨ False) → False) ∧ (p5 ∧ p2))) ∧ (((p5 ∨ False) → False) → p5)) ∨ ((True ∨ ((p4 → p4) ∨ False)) ∧ ((True ∨ p5) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187735689912028455101264187978 : ((p1 → (p3 ∧ (((((p1 → p4) ∧ p4) ∧ True) ∧ p5) ∨ p3))) → ((p1 ∧ p3) → (p4 ∨ (((p5 → p2) → ((p1 ∨ p3) → p3)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204146875228260290488737608950 : (((((p3 ∧ p5) ∧ p2) ∨ p5) ∧ p5) ∨ ((p2 ∧ (p3 ∧ (p3 ∧ p2))) → ((p1 ∨ (((p2 ∧ True) → p5) → ((True → p3) ∧ p2))) ∧ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224274598935326726454136543923 : ((False → (p1 ∧ False)) ∧ ((((p3 → (p5 ∧ (p4 → p1))) ∧ (p5 ∧ p1)) → True) → ((((False → p3) → (p5 ∧ p2)) ∨ (p1 → p1)) ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136268277018721341790869067562 : (((((True ∧ (p4 ∧ p2)) ∧ p1) → False) → (((p2 → p4) ∨ (((p1 ∧ True) ∨ False) ∧ True)) → (p5 → (p3 ∧ False)))) ∨ (True ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678224124793769731112075141407 : (((((p1 ∧ (True ∧ ((p3 → (False ∨ (p5 ∨ p4))) ∧ False))) ∨ (p3 ∧ ((False ∧ (p5 → p1)) → p1))) ∨ (((p5 ∧ True) → p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164811153845378409361547472129 : ((((p1 ∨ p3) ∧ (((((False ∧ p3) → (p2 ∧ (p3 → p4))) → p1) ∧ p2) ∧ p3)) ∨ p4) ∨ (p4 → (p5 → (p1 → (p5 ∨ (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52540618931676736583955661100 : ((((p3 → ((p5 ∧ (p5 ∧ p3)) ∨ ((p1 ∨ (False ∧ p4)) → p4))) ∨ p2) ∨ (((True → ((p4 ∧ False) ∨ False)) ∨ (p3 ∧ p5)) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141315709541951621270080846821 : (((((p1 ∧ p4) ∧ p1) ∧ p1) ∨ ((False ∨ (p3 → p4)) ∧ ((p4 → (p3 ∧ ((p3 → p2) → (False ∨ p2)))) → True))) → (p2 ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317633629812175525014914587797 : (p4 ∨ (((((p3 → p5) ∧ (True ∧ (p1 ∧ (True ∨ p2)))) → ((p2 ∨ ((p4 → ((p2 ∨ True) → False)) → p3)) ∨ (False → p2))) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230567635683594165379845867473 : (((p1 → False) ∧ p1) → (((p3 ∧ (p4 ∨ p4)) ∨ (((p2 → p1) → (p2 → (p1 ∧ p4))) ∧ p4)) → (((p2 ∧ False) ∨ p1) ∨ (p5 ∨ True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183495148184502772889112797053 : ((p3 ∨ (False → ((True → (p4 ∧ (True → (p3 ∧ p4)))) ∧ p5))) ∧ (p1 ∨ (((((p2 → p3) ∨ p5) → False) ∨ p2) ∨ ((p1 ∨ p5) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2309694657723938768932348133 : ((((True → p4) ∨ (p4 ∧ (((p4 → True) ∧ p5) → p4))) ∨ (p5 → p3)) → ((True ∧ (p2 ∨ ((p3 ∧ p5) ∧ (p3 → p3)))) ∨ True)) := by
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
theorem thm_5_vars_60658085993586545887286877486 : ((True ∧ ((p2 ∨ (((p2 ∧ p2) → True) ∧ ((((p4 ∨ (p4 ∧ p2)) ∧ (p3 ∧ p2)) → False) ∧ False))) ∨ (p1 → (p2 ∨ (True ∨ True))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338626446178289994873037065840 : (p1 → ((p1 → (p5 ∧ False)) → ((((True ∨ p5) ∧ False) ∨ p4) ∨ (((True ∧ ((p3 → (p5 ∧ p3)) → (True ∧ False))) → p2) → (p5 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56651630040825313421643210131 : ((((p2 ∨ p5) ∧ p2) ∧ ((((p3 → ((p5 ∨ p5) ∧ p5)) ∧ (p2 ∨ p1)) ∨ ((p2 ∨ (p4 ∨ p4)) → (p4 ∧ (p1 → True)))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197632918877173595581321311331 : (((((p1 → p5) ∨ True) ∨ p4) → (p1 ∧ p5)) ∨ (((((p5 ∧ (((False ∨ p1) ∨ ((p5 → p1) ∧ p3)) → False)) → p2) ∧ p1) ∧ p1) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152463810897610723508082969016 : (((p4 ∨ (p4 ∨ p3)) ∧ ((((p1 ∧ p2) ∧ (False ∨ (True ∧ p2))) ∨ (p2 ∧ (p3 ∧ (True ∨ p3)))) ∨ p4)) → (p1 ∨ (False → (p1 ∨ True)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- False on the left can always be used.
          apply False.elim h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h30.left
          let h33 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h31
          case inl h34 =>
            -- False on the left can always be used.
            apply False.elim h34
          case inr h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Disjunctions on the left can always be decomposed.
          cases h42
          case inl h43 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h44
            -- False on the left can always be used.
            apply False.elim h44
          case inr h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h46
            -- False on the left can always be used.
            apply False.elim h46
      case inr h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h48
        -- False on the left can always be used.
        apply False.elim h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- Conjunctions on the left can always be decomposed.
          let h54 := h52.left
          let h55 := h52.right
          -- Disjunctions on the left can always be decomposed.
          cases h53
          case inl h56 =>
            -- False on the left can always be used.
            apply False.elim h56
          case inr h57 =>
            -- Conjunctions on the left can always be decomposed.
            let h58 := h57.left
            let h59 := h57.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h54
        case inr h60 =>
          -- Conjunctions on the left can always be decomposed.
          let h61 := h60.left
          let h62 := h60.right
          -- Conjunctions on the left can always be decomposed.
          let h63 := h62.left
          let h64 := h62.right
          -- Disjunctions on the left can always be decomposed.
          cases h64
          case inl h65 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h66
            -- False on the left can always be used.
            apply False.elim h66
          case inr h67 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h68
            -- False on the left can always be used.
            apply False.elim h68
      case inr h69 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h70
        -- False on the left can always be used.
        apply False.elim h70



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308936275520282605377715970042 : (p2 ∨ (((((p2 ∨ (((p5 ∧ ((p1 → (p2 → p1)) ∨ p2)) ∧ p3) → p4)) ∨ False) → p3) ∧ (((p3 ∨ (p4 ∨ p3)) → p3) → p3)) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ (p4 ∨ p3)) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : ((p2 ∨ (((p5 ∧ ((p1 → (p2 → p1)) ∨ p2)) ∧ p3) → p4)) ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- One of the premise coincides with the conclusion.
            exact h8
          case inr h16 =>
            -- One of the premise coincides with the conclusion.
            exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h17 := h2 h9
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h18
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h19 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330295040037205622585521581431 : (True → (p1 ∨ (((((True ∧ p5) ∨ p5) ∧ (False ∧ (p2 → ((p5 ∧ p5) → ((((p1 ∨ (p5 → p2)) ∧ p3) → p1) ∧ p3))))) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_190800682904719018996044392030 : ((((p3 → (p4 ∨ False)) → (p3 ∨ p4)) ∨ (p3 ∨ False)) ∨ ((((True ∧ False) → True) ∨ p2) ∨ (p1 ∨ ((p3 → (p5 → p1)) ∧ (p5 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187562611947699164069374175218 : ((p2 ∨ (p4 → (((p5 ∨ (False → p2)) → False) ∨ (p3 ∧ p5)))) → ((p5 ∧ ((p2 ∧ True) ∧ (p3 ∨ True))) → (p2 ∧ ((p1 ∧ p3) ∨ p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h17.left
  let h20 := h17.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h26 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686054209828713708180501887304 : ((((((p3 ∨ p4) ∨ (p3 → (p4 → ((p4 ∧ (p5 ∧ False)) → (p1 → True))))) → (False ∧ False)) → ((p1 ∧ ((p4 ∨ p5) ∧ p5)) → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : ((p3 ∨ p4) ∨ (p3 → (p4 → ((p4 ∧ (p5 ∧ False)) → (p1 → True))))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : ((p3 ∨ p4) ∨ (p3 → (p4 → ((p4 ∧ (p5 ∧ False)) → (p1 → True))))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h17 := h1 h12
    -- We need to get the left conjuct of h17 based on <expert-advice>.
    let h18 := h17.left
    -- False on the left can always be used.
    apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246642089363438163002765113402 : ((p5 ∧ p3) ∨ (((p4 ∧ (p5 ∧ (p5 ∧ True))) ∨ (p2 → (p1 ∨ p4))) → ((((False ∨ (p2 ∨ True)) ∨ False) ∨ (p2 ∧ (False ∧ True))) ∨ p4))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147000924745165682874362258152 : ((((p1 ∧ (((True ∧ (p1 ∧ (p4 ∧ (p1 ∨ p5)))) → (p2 ∧ (p1 → True))) ∧ p4)) ∧ (False → p1)) ∧ p5) ∨ ((p4 ∨ (p1 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670283846479438708564767702024 : (((((p2 → (p1 → (p2 ∨ p3))) → ((((p2 → p1) → p5) → (False → ((p4 ∨ p3) ∧ True))) ∧ (p1 ∧ p5))) ∨ (p1 ∨ (p5 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156868315527444979897578911932 : ((((((p5 → False) ∧ p5) → (((((p1 ∧ (False → True)) ∨ p4) ∨ False) ∨ p4) ∨ p2)) ∧ False) ∨ True) ∨ ((True ∨ p3) ∨ ((True ∧ p2) ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54123213208612728438337537640 : (((False ∨ (((((False ∨ True) → True) ∧ p5) ∨ p2) → p3)) → (p4 → (False ∨ ((p5 → (p2 ∧ (True → (p5 → p1)))) ∨ (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66169676334051303000027084821 : ((p5 ∨ ((p2 → (((p2 ∧ (p2 ∨ (((p2 ∨ p4) ∨ (p3 ∧ ((p2 → False) → p2))) ∧ p4))) ∧ p4) → p3)) ∨ (p5 ∨ (p3 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247866744289811628239755174433 : ((p1 ∨ p2) ∨ ((p2 ∨ p1) ∨ (((p2 → (True → ((p2 → (p4 ∨ ((p3 ∨ (p2 ∧ ((p1 → p2) ∨ p5))) ∧ False))) ∨ True))) ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52443379228479573079386733533 : (((p1 ∧ ((p2 → (p1 → (((p4 → False) ∧ True) ∧ True))) ∧ (p3 ∧ p5))) ∧ (p3 ∧ ((p5 → (p1 ∨ p2)) → ((p4 ∨ True) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61749185132975740651930063735 : ((p1 ∧ (p4 → (True → ((p3 → ((((False → (p3 ∧ p1)) ∨ ((False ∧ p5) ∧ ((True ∨ (p4 ∨ True)) ∧ p5))) ∧ p5) → p2)) → p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186729500225245912069671795255 : (((p5 ∨ ((p1 ∨ (p1 → p1)) → True)) ∨ (p5 ∨ (p3 → p4))) → ((True → ((p2 → p4) → (((p2 → p5) ∧ True) ∨ p3))) ∨ (p2 → p2))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38212266038961710107556927335 : (((((p3 ∨ (p2 → ((p2 → p2) ∨ (False ∨ (p1 ∨ False))))) → (p4 → ((False → True) ∧ (p5 ∧ p3)))) → ((True → p2) → p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37549276825569614945964827346 : ((((False ∨ (((((((p4 ∨ p5) ∨ False) ∧ True) → (False ∨ p1)) ∧ (p5 ∧ ((p2 ∨ p4) ∨ (True ∨ p5)))) ∨ p1) ∧ False)) ∨ False) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301375145742354275961982385206 : (False ∨ (((p4 ∨ (p5 → p1)) → False) ∨ ((p1 → p3) → ((p2 → ((((p1 ∧ False) ∨ ((p4 ∨ p1) ∨ False)) → (p4 ∨ p5)) ∨ True)) → True)))) := by
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
theorem thm_5_vars_165456576678420769558608289921 : ((((p3 ∧ ((True → p4) ∨ p2)) ∧ (p4 → (True ∧ p3))) ∧ (p5 ∨ ((True ∨ p1) → p4))) ∨ (p2 → ((((p2 ∨ p1) ∧ False) ∧ p1) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343629852447705955633154050745 : (p2 → (True ∧ ((((True → p2) → (((p3 ∨ p3) ∨ ((p4 ∨ p5) ∧ ((True ∧ (p1 → p3)) ∨ p3))) ∧ (True → p2))) ∨ p2) ∨ (p4 ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643162055640695308852117598461 : ((((p3 ∧ ((False ∧ (((p5 → p3) ∨ (((False ∨ ((((p4 → p4) ∨ p2) ∧ p4) → p5)) ∨ False) ∨ False)) ∧ (p4 ∧ p1))) → True)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49851165176691360621640388958 : ((((((p3 ∨ ((p3 ∧ True) → p5)) → (p1 → (((p4 ∨ True) ∧ p4) ∧ p1))) ∧ (p5 → p3)) ∧ True) ∧ (False → (p3 ∧ (p1 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113779149850114369420760557270 : (((((p1 → p3) ∧ False) ∨ (p1 ∨ (False → ((p3 ∨ True) → (p2 ∨ ((p1 → ((False ∧ p1) ∧ p2)) → p3)))))) → (p1 ∨ p2)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54863605852224376211772540059 : (((((False → p2) → (p1 ∨ False)) ∧ p2) ∧ (((p4 → True) → (p3 ∧ p2)) → (True → ((True ∧ p4) ∧ (p2 ∧ ((p1 → p4) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_450914447805633035787001095363 : ((((((p1 → (((p1 → (p4 ∨ p2)) ∨ (True ∧ (False → True))) ∨ (p4 ∧ p1))) → (p1 ∨ False)) ∨ p5) ∨ (((p5 → False) ∧ False) → False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62718652043736494941920276177 : ((p4 ∧ ((p3 ∨ (((p1 → ((p3 ∨ p4) ∨ p5)) ∧ p1) → ((False ∧ (p2 ∧ (False → False))) ∨ ((True ∨ (p5 ∧ p3)) ∧ p2)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248405414403669866382688764838 : ((p2 ∨ p4) ∨ (((p2 → ((True ∧ p1) ∨ p5)) ∧ p3) ∨ (True ∨ ((p1 → (((((p5 ∨ False) ∧ False) ∧ True) ∧ (p4 ∨ p2)) ∧ False)) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47323558862037348907405008161 : ((((True ∧ (p3 → p3)) → (((p1 ∨ ((False ∨ p1) → (p5 ∨ p2))) ∧ (((p3 ∨ (p3 ∨ True)) → True) ∨ p3)) ∨ True)) ∨ (p4 ∧ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_612322019002194857780938649436 : (((((p3 ∧ ((p2 ∧ ((False → p5) → p3)) ∨ ((p3 ∨ p5) ∧ ((True → p3) ∨ (p3 ∧ ((p2 ∨ p4) ∧ p2)))))) ∧ (p2 ∨ p3)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134117733175020292017403212439 : ((((((((((p5 → p3) ∨ p4) ∨ (p3 ∧ p5)) ∨ (p4 ∨ p5)) ∨ p2) ∨ (p2 ∨ p4)) ∨ True) ∨ (False ∨ False)) ∨ p4) ∨ (p2 ∨ (p2 ∨ p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218480967265695007097320056058 : (((False ∨ False) → (p2 ∧ p5)) → (((((False ∧ p4) ∧ (((((p3 ∧ p5) → True) → True) ∨ (p3 → (p4 → p2))) ∧ p1)) ∨ p5) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53069654430787340986437559454 : (((p1 ∧ (p1 ∨ (((p5 ∧ p2) ∧ ((p1 ∧ False) ∧ p4)) ∨ p1))) ∧ ((p5 → ((p3 ∨ p3) ∧ ((True ∨ p3) ∧ p4))) ∧ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357474625274275263182319666539 : (p5 → ((p4 → p5) → (p1 → ((p2 ∧ (((p2 ∨ p2) ∧ p3) ∨ (((p3 ∨ (p1 ∨ p5)) → p3) → p2))) ∨ ((p2 ∧ False) → (p4 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_823682243917260414795592567531 : (((((((p3 → True) → p1) ∧ True) ∧ (((p2 ∨ p1) ∧ ((p3 → True) ∨ (((p1 ∧ (p4 ∧ p5)) → p3) → False))) ∨ (True → p1))) ∧ True) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h15 := h6 h13
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h17 : (p3 → True) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h19 := h6 h17
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h21 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h20
  case inr h23 =>
    -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h23, we can now drive its conclusion.
    let h25 := h23 h24
    -- One of the premise coincides with the conclusion.
    exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148953847515805575945982773074 : ((((p3 ∨ p3) ∧ p5) ∧ (False ∨ ((False → ((p2 → p1) ∧ True)) → (((True ∨ (p3 ∨ True)) → p3) ∧ False)))) ∨ (p1 ∨ ((p1 → p1) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789626785459829093947192453536 : (((p5 ∨ (((((p3 → p1) ∧ p3) → p3) ∧ p5) ∧ (p2 ∧ (((p1 ∨ ((p2 ∧ p1) ∨ (True ∨ (False ∧ p3)))) ∨ (p3 ∨ p1)) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191603760238070415396112536780 : ((p3 ∧ (((p4 → (p5 ∨ (True → p5))) ∧ p4) → p3)) ∨ (p3 → ((p3 → (p1 → ((p1 ∧ p1) ∨ (False → p1)))) ∨ ((p4 ∧ p2) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217429094116986516212203117430 : (((p2 → (False → p1)) ∨ False) → ((((((p1 ∨ p5) ∧ p4) ∨ p4) ∧ p4) ∧ (((p3 ∧ True) ∧ p4) ∨ True)) ∨ (((p5 ∨ False) ∨ True) ∨ p4))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427520229503858844265090996293 : (((((p5 ∨ (p3 ∧ (p2 ∨ (((((p5 → ((p5 → p4) ∨ p2)) → p3) ∧ (True ∧ True)) ∨ True) ∨ (p5 → p3))))) ∧ True) ∨ (p3 ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669115443543390115657986495461 : ((((((False ∨ (((p3 ∨ True) ∧ True) → (False ∧ (False ∨ (False → False))))) ∧ ((p2 ∧ (p5 ∧ p3)) → p4)) → p3) ∨ ((True → True) ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193434068543830193953316642288 : (((True → p3) ∧ ((p2 ∧ ((False ∨ True) ∨ p5)) → False)) → (((p1 → (p3 ∧ ((False → False) ∧ p5))) → p5) → (False ∨ ((p2 ∨ p3) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174626415820273384347375253755 : ((((True → p5) ∨ (p3 ∨ p2)) → ((p5 → (p5 ∨ (p3 ∨ (p2 → p5)))) ∧ False)) → (((p5 → p1) ∧ (((p5 ∧ False) ∧ p2) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198402654808964697304034067820 : ((p4 ∧ (((p1 ∨ (p4 → p5)) ∨ False) ∧ p4)) ∨ ((p4 ∨ (p4 ∨ ((p5 ∨ (((p4 ∧ (p3 ∨ p4)) → False) ∨ p4)) ∨ (True → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340026931980426483567479188387 : (p1 → (p2 → ((((p3 ∨ ((False ∧ ((True ∨ p5) ∨ p1)) ∨ p3)) ∨ ((p3 ∧ p2) ∧ (p5 → (p4 → ((False ∧ False) ∨ p5))))) ∨ True) ∨ False))) := by
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
theorem thm_5_vars_111767141755915364025460064604 : (((((False ∧ (False ∧ p2)) ∨ (((p2 ∧ True) → ((p4 ∧ False) ∧ p1)) → ((p1 → p5) → (False ∨ p1)))) ∧ (p1 ∨ True)) ∨ p5) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42699433606055622957910180391 : (((p5 ∨ (((False → (((True ∨ (False ∨ p3)) ∨ ((p5 ∧ True) → True)) ∧ (True ∧ p2))) → p2) → (p4 ∨ ((p1 ∧ True) ∨ p1)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148190355676303717410724078821 : ((((p4 ∨ ((p2 ∨ True) ∨ (p3 ∧ p4))) → (False ∨ ((p1 ∨ p5) ∧ (p5 ∨ p3)))) ∧ ((True ∨ p4) ∧ p2)) ∨ ((p4 ∨ p1) ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161896787854165856549520659868 : ((False → (p1 → (p5 ∧ (p3 ∨ (((True → ((p3 → (p5 → p4)) ∨ p1)) ∨ p5) ∧ (p4 ∨ p5)))))) → ((p5 ∨ p3) ∨ ((p3 → p4) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134148579796737980964056601221 : ((((((((p3 ∧ p2) ∨ p2) ∨ ((p1 ∨ True) ∨ p2)) → ((True ∧ True) ∧ p3)) ∧ p5) ∨ ((p4 ∧ True) → p3)) ∨ p2) ∨ (False → (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743312542741734624388722138300 : ((((p5 → False) ∨ ((((p1 ∧ True) ∧ (p5 ∧ ((p1 ∧ p2) → (False ∧ p4)))) ∧ (True → (True ∧ (p5 ∧ (True ∨ p5))))) ∧ (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328277774302404345427666719485 : (True → (((p4 → ((p5 → (((p5 ∧ (p2 ∨ p3)) ∨ False) ∧ (p4 ∨ (False ∧ True)))) → (False ∧ p1))) ∨ p4) ∨ ((p3 ∧ (p3 → p2)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213580123131579248400883136005 : ((((p5 ∨ p2) ∧ p2) ∨ p1) ∨ (p3 → ((p3 ∧ ((((p2 ∧ True) ∨ (p1 ∨ False)) → ((True ∨ False) → p5)) → ((p1 ∨ p2) ∧ p1))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



