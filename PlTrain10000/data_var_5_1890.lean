variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715820899009579392532791267035 : ((((((False → p3) → p1) ∨ True) ∧ ((p5 → (True ∧ p3)) → (((p2 → (False → p5)) ∧ ((p2 ∨ p3) ∧ p2)) ∧ ((False → False) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263706926678018051522595445714 : (True ∧ ((p5 ∧ ((True → (p2 ∨ (p2 ∨ ((True ∨ (p4 ∨ (p4 ∨ p3))) ∧ (p2 → p1))))) → p3)) ∨ ((False ∧ p2) → ((p1 ∨ p5) ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_245129846353678861558525045261 : ((p2 ∧ True) ∨ (((p1 ∨ True) ∧ p5) ∨ (((p1 ∨ True) → (False ∨ ((True ∨ ((p2 ∧ (p2 → (p5 ∨ (p2 → p5)))) ∧ p4)) ∨ p2))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50131636796679684625632039514 : (((p4 ∨ ((p2 ∨ p1) ∨ ((False ∨ False) ∨ ((p4 ∧ ((False → p1) ∧ p4)) → (p4 ∧ (p3 ∧ False)))))) ∧ (False ∧ (p2 → (p3 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41029496799902406468933024591 : (((((((False ∨ (((p2 ∨ True) ∧ False) ∨ p3)) ∧ p4) ∧ (((False ∨ p5) ∨ (p1 → False)) ∨ True)) → (p3 ∨ p5)) → (p2 → p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338051178108580369558291603221 : (p1 → ((p2 ∨ (p3 ∨ ((((p2 → False) ∧ p5) ∧ False) ∧ p1))) ∨ (False ∨ (((True ∨ (p1 ∨ p2)) ∨ (p1 ∨ p1)) → ((True ∨ p5) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165078831984598619774025914204 : (((True ∨ (((((True ∨ p3) → True) ∨ (p2 ∨ p2)) → (p4 ∨ p5)) → (p3 ∧ p5))) → p2) ∨ ((False ∨ False) → (p3 → (p2 ∨ (p1 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258383351532001084726525383421 : ((p5 ∨ False) → (p1 ∨ (p2 → ((p3 ∨ (((False ∨ ((p3 ∨ p2) ∨ p2)) ∧ p4) ∨ (True ∧ p5))) ∨ ((p4 → ((p4 ∧ p3) → False)) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606930157854177581212763163077 : (((((((p5 ∨ p5) ∨ (True → (p5 ∧ ((False ∧ (p2 ∧ p1)) ∨ ((False ∨ False) ∨ True))))) ∨ (p4 ∧ (p3 ∨ (p1 ∧ p2)))) ∧ p1) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137344486243920666262374537376 : ((p2 ∧ (p4 → (p5 → (((False ∨ p1) → (False → (p2 ∧ True))) → ((False → p5) → ((p1 → (False → p1)) → p2)))))) ∨ (False → (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64961107974177126509476732181 : ((p2 ∨ ((True ∧ ((((True ∨ p5) → False) ∧ p5) ∧ p4)) → (p4 → ((p2 ∨ (p2 ∧ (p4 ∨ (p1 ∧ (p5 ∨ p4))))) ∧ (p2 ∧ p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
  have h17 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h15, we can now drive its conclusion.
  let h18 := h15 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- One of the premise coincides with the conclusion.
  exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199927672393919982885527654248 : ((((p5 → p2) ∨ (p1 ∧ p3)) ∨ (p3 ∧ p2)) → (True ∧ (p5 → (p4 → (p5 → ((False ∧ False) ∨ (((True → (p2 ∨ True)) → p4) ∨ True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178346608490804709753506238397 : (((False ∧ (False ∨ (p2 ∨ (True ∨ ((False ∧ p5) ∧ True))))) ∨ (p1 ∨ p3)) ∨ ((p3 ∨ (False → (((p4 ∧ False) → (p4 ∨ p3)) ∧ p1))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178533982023591436220763742377 : ((((p1 ∨ p1) → (p3 ∧ ((False ∨ p5) ∨ p2))) → ((p3 ∧ p1) ∧ p5)) ∨ (p3 → (True ∧ ((p4 ∨ ((False → (p3 ∨ p2)) → p5)) ∨ True)))) := by
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
theorem thm_5_vars_358555473253019156996018263066 : (p5 → (p2 → ((p5 ∧ p2) → (((((False → p5) ∨ p3) ∧ ((p4 ∨ p5) ∧ (p4 ∨ p1))) ∧ (p1 ∨ (p1 → (p4 ∨ p5)))) ∨ (p4 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153493672354288890040671993669 : ((p5 ∨ (((((p5 → True) ∨ p3) → (False ∧ p1)) ∧ p4) ∨ (p2 → ((((p3 ∨ p4) ∨ True) → p2) → p2)))) → (p4 ∨ ((p3 → p4) ∨ True))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352833701795449692491977938429 : (p4 → ((p1 → p4) → ((True → p3) ∨ ((((p1 ∨ p2) ∧ p2) ∨ ((True → p5) ∨ False)) ∨ (((p1 ∨ True) ∨ (p3 → p3)) ∨ (False ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60750209983019330353944575953 : ((True ∧ (((False ∨ p1) → p5) → (((((((((p3 → (p1 → True)) ∨ False) ∧ (p3 ∨ p1)) → p3) ∨ True) ∧ p5) ∨ p2) ∨ p1) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157460102301170692217573432727 : (((((p3 ∧ ((p5 → ((p1 ∨ (p4 ∨ p4)) ∨ p4)) ∧ (p5 ∧ False))) ∧ p1) ∨ True) ∨ (False ∨ p3)) ∨ (((False ∨ p2) ∨ (p4 ∨ p2)) ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137326165975551584519557125233 : ((p2 ∧ ((True → p4) → ((((True → True) → (((p1 ∧ p3) → p3) → True)) ∨ p4) ∧ (((p4 → False) ∧ True) ∧ p2)))) ∨ ((p2 → p2) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_579836898664658538729314988093 : (((p4 → ((False ∨ ((((False → (((True ∨ p1) ∨ p5) ∧ p2)) → (True ∧ True)) → ((True ∨ (p4 ∨ True)) → (p1 ∨ p2))) ∧ True)) ∨ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312883632799334035125346023266 : (p3 ∨ ((p1 ∨ ((((p1 ∨ False) → p2) → (p2 → (p2 → ((False ∨ (True ∧ ((False ∧ (p4 ∧ True)) → (p4 → True)))) ∧ p2)))) ∨ p2)) ∧ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57851431138124801624532206141 : (((True ∨ (p2 ∨ p2)) → (p1 ∨ (((p5 ∨ True) ∧ (((p1 ∨ False) → p1) ∨ ((p3 ∨ (((p4 ∧ p1) → True) ∨ True)) ∨ True))) ∨ True))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_642783673314880300997093449772 : ((((p1 ∧ (p4 ∨ (((False → ((p5 → False) ∨ p3)) → (True ∧ (p1 ∧ ((False ∨ (False ∨ p2)) → ((p4 → True) → p4))))) ∨ p3))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51798914066605787691521832193 : (((p1 ∨ ((p2 ∨ p1) → (p4 → ((((p3 ∨ True) ∧ (True → True)) → False) → p2)))) ∧ (p3 → ((p4 ∧ (p1 ∨ (p4 → p2))) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357202045774162049402403950466 : (p5 → ((p5 ∨ p2) ∧ (((p4 → p1) ∨ p1) ∨ (p2 → (((False ∨ (((p3 ∧ p4) → (p3 ∧ p2)) ∧ (False → p4))) → p1) ∨ (False ∨ p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304029622370569375897130607751 : (p1 ∨ ((p2 ∧ ((p5 → (((p2 ∨ ((p5 ∧ False) → ((True ∨ p3) ∧ (p5 ∨ p5)))) → (((p4 ∨ p2) ∧ p5) ∨ p1)) → p2)) → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309948377415796213842390588277 : (p2 ∨ (((p1 → (p2 ∨ (p1 → (((p3 ∧ (p4 ∨ (p2 ∨ True))) → True) ∨ (p3 ∨ p5))))) ∧ p2) → (((True ∧ p4) → False) ∨ (p2 ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148425773698646566280933378464 : ((((p1 ∧ ((p1 ∧ p1) ∨ p4)) → ((p5 ∧ (True ∨ False)) → (False → p2))) → ((p2 ∧ (p5 → False)) ∧ False)) ∨ (((p5 ∧ p1) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241456792395734904232256726459 : ((False → p2) ∧ (((((True → (p3 ∨ (p1 ∧ (False → p1)))) ∨ (p5 ∨ p3)) ∨ (p1 → p5)) ∨ (True → (p3 ∨ (p3 → (p3 ∨ False))))) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252629364014617681529722504502 : ((p5 → p4) ∨ (((((p3 ∨ p3) ∧ p5) ∧ ((False ∧ True) ∨ (((p4 → p2) ∧ (p5 ∨ (p1 → False))) ∧ (p4 ∨ (True → True))))) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159179162608018562341348545601 : ((p1 → (False ∧ ((p3 ∧ p4) ∧ ((p3 → (p1 ∧ ((p5 ∧ False) → (p5 → p5)))) → (True → p5))))) ∨ ((p3 → True) ∨ ((p1 ∧ p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135742883502119758548141858147 : ((((p1 ∨ ((False ∨ (p5 → False)) ∧ p1)) ∧ (((p1 ∧ False) → p2) → True)) ∨ ((p1 ∨ ((p1 → p4) → True)) ∨ p5)) ∨ ((True → p2) → p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192500463390567191962178401549 : ((((p1 ∧ True) ∧ (p5 ∧ (False → (p5 ∧ True)))) ∨ True) → ((p3 ∨ ((p5 ∧ p4) → p2)) → ((p2 ∧ True) → ((True → (False ∨ False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h17.left
      let h20 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h18.left
      let h22 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232401394023734151870000103248 : (((p5 → p4) → p2) → (((p1 ∨ ((False → True) → (p5 ∧ (p3 → p1)))) ∧ ((p2 → ((p4 ∧ p2) → ((p3 ∧ p2) ∨ False))) ∧ p3)) → p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h4.left
    let h10 := h4.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (False → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137205515707845876085267429906 : ((False ∧ (p4 ∨ (((True ∧ (p5 → p3)) ∨ ((p4 → (True ∧ p1)) ∧ (p1 ∧ p1))) → (p2 → ((p3 → p4) ∨ p5))))) ∨ (True ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52240812937969348179847690055 : (((p4 ∧ (p2 ∧ (((p2 ∧ p4) ∨ (p5 ∨ (p3 ∧ p5))) → (p3 ∧ (p3 → p2))))) → ((p3 ∨ (((p2 ∨ True) ∨ True) → p5)) ∨ False)) ∨ p4) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 ∧ p4) ∨ (p5 ∨ (p3 ∧ p5))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171581160251731233432176560913 : (((((((p1 ∨ p3) → p4) ∧ True) ∨ (p3 ∧ (p3 ∧ p3))) → (p4 ∨ p5)) ∨ p4) ∨ (p4 → (False → ((True ∧ (False ∨ p5)) ∧ (p3 ∨ p1))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133656362057365062090754575946 : ((((((p3 ∨ (True ∨ p1)) ∨ (p5 → ((p3 → (p3 ∧ True)) ∨ (p1 → (p1 → p4))))) → p2) ∨ (p4 → p3)) ∧ p5) ∨ (False → (False ∧ p4))) := by
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
theorem thm_5_vars_748271554960917114013105070530 : ((((p2 → False) → ((p3 → (p2 → (((((True ∨ (p5 ∨ False)) ∨ ((False ∧ False) ∨ p4)) → p5) ∧ (p1 ∧ (p5 ∧ False))) ∨ p2))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656695561312467999160649922916 : ((((((p3 ∨ p3) → ((p5 ∧ p4) ∨ True)) ∧ ((False ∨ ((((p1 ∨ ((True ∨ p4) ∨ p5)) ∨ p4) ∧ True) ∨ p1)) ∨ p2)) ∨ (p4 ∧ p2)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_720967048937304003258736915001 : (((((p5 ∨ p1) ∧ (True ∧ p5)) → ((((p2 → (((p3 ∨ True) → p3) ∨ p1)) → False) ∨ (p1 ∧ False)) ∨ (p5 ∨ ((p3 ∨ p2) ∨ p3)))) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760966219893298460728165065447 : (((p2 ∧ (True → ((((((p1 ∧ ((False ∨ p1) → (True ∧ (p5 → True)))) → p4) ∧ (True ∨ p3)) ∨ p5) ∧ p2) → ((p5 ∧ p4) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185626437229140637837259059832 : ((True → (True ∧ (p3 ∨ (((p3 ∨ p1) ∨ (p2 ∨ p1)) ∧ p5)))) ∨ (True ∨ ((p5 → p1) ∧ ((p1 → False) ∧ ((p2 → p3) ∨ (p3 → False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142527519426525966356507453752 : ((True ∨ ((((((False → (((p4 → True) → False) → p3)) → True) → p1) ∨ (p4 → p5)) ∨ False) ∧ ((False → p5) ∨ p3))) → ((p2 ∨ p4) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h11 =>
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
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136245697488353265205262189957 : (((p4 ∧ (p2 ∧ (p2 ∨ (p1 ∧ True)))) ∨ (p1 ∨ (False → (p5 → ((p3 → (False ∧ p1)) ∨ ((p5 ∧ p2) ∨ p5)))))) ∨ (p1 ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54116886112602409412715571158 : (((p5 ∧ (((p2 → (False → (True ∧ True))) ∨ p4) → p3)) → ((p3 ∧ (((p3 ∧ p3) ∧ (p5 → p4)) ∨ p1)) ∧ (False → (False ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199068401610212717104602987797 : (((((p1 ∧ (p5 ∧ p1)) ∨ True) → False) ∧ p5) → ((((p3 ∧ ((True ∧ ((p1 ∧ p4) → True)) ∧ (False ∧ p5))) → p2) ∨ False) → (p4 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∧ (p5 ∧ p1)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : ((p1 ∧ (p5 ∧ p1)) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792701141338753477350866733786 : (((True → ((False ∨ ((p4 → p2) → p5)) ∧ (((p1 ∧ False) → ((p2 ∨ p1) ∧ (p2 → (((p3 → p4) → p3) → (p1 → p3))))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197452625765116484750541786071 : ((((p5 ∨ (p2 → p3)) ∨ p1) ∧ (p5 → True)) ∨ (((False → False) → (p2 ∧ (p3 → p5))) ∨ (False → (p3 → ((p2 → (p2 ∨ p5)) ∧ True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639342437320097718162961305846 : ((((((True ∨ False) ∨ (p1 ∨ p3)) → (((False ∨ ((p2 → (((False ∧ False) → p4) → (p3 ∧ (p3 → p3)))) ∧ False)) → p1) ∨ False)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343583050755774461050972078778 : (p2 → ((p1 → True) → (((((p1 ∨ (p3 → (True → p2))) → p3) ∧ ((p3 ∧ (((p2 ∧ p3) ∨ p1) ∨ (False ∧ p4))) ∧ False)) ∨ p2) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134278581419108376075447684559 : ((((p3 → p3) ∧ (((((p3 → (p5 → p5)) ∧ p1) ∨ (False ∨ (p1 ∧ (False → p2)))) → (False ∧ True)) ∧ p2)) ∨ p1) ∨ ((p3 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245722485944851990856267196418 : ((p3 ∧ p2) ∨ (((((((p1 ∨ p3) ∨ p2) ∧ (p5 → ((p5 → True) ∨ (p2 ∨ p3)))) ∨ p3) ∨ p2) ∨ (p4 ∨ True)) ∨ ((False ∧ p3) ∧ False))) := by
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
theorem thm_5_vars_56367115358595026769599308611 : ((((p1 → (p4 ∨ p4)) ∨ p2) → ((True → ((((True ∨ p1) → (False → False)) ∨ p2) ∨ (True → (p3 → False)))) → ((p2 → p5) ∨ True))) ∨ p5) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721800143920980579626688330877 : ((((p2 ∨ (p5 ∨ (p1 ∨ p2))) → (p2 ∨ (p4 ∧ (((p5 → (False ∧ (p4 ∨ False))) → (p5 ∨ (True ∧ ((True ∧ p4) → False)))) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125340755603140403123665461177 : (((p1 ∨ (p4 ∨ p4)) → ((True ∨ ((p4 ∨ (p5 ∧ True)) ∧ (p3 → True))) ∨ ((False ∧ p5) ∨ (((False ∧ p4) → p1) → p2)))) → (p2 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261448667857668930680111547291 : ((p5 → p2) → ((p3 → ((((p3 ∨ p2) → (True ∧ p4)) ∨ ((True ∧ (False → ((p2 ∧ (True → False)) ∨ False))) ∧ p3)) ∨ p4)) ∨ (p4 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644704418915876493353328441 : (((((((p3 ∧ ((False ∨ False) ∧ p3)) ∧ (False → (p1 ∨ p1))) ∨ (p1 ∧ (False → p4))) ∨ p2) ∨ p5) ∨ ((True ∧ False) → p4)) ∨ p4) := by
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
theorem thm_5_vars_183868719910742922153133460365 : (((((p4 ∧ (True ∧ p3)) ∨ p5) → (False ∨ (p2 ∨ False))) ∧ False) ∨ ((True → False) ∨ (((p3 ∧ p4) ∨ (True ∧ True)) ∨ (p2 ∧ (False → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_119550411678031443429165672429 : ((p5 → (((True → p3) ∨ (False ∧ (p4 ∨ (((p5 → (p5 → (True → True))) ∧ (True ∨ p5)) → False)))) ∨ (True ∨ (p2 ∨ p2)))) ∨ (False ∧ False)) := by
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
theorem thm_5_vars_248286574527187833970677526798 : ((p2 ∨ p2) ∨ (((p2 → p3) → (p1 ∨ p2)) → ((p4 → p5) → ((p4 → ((p1 ∨ p2) ∨ ((False ∧ p3) ∨ p4))) ∨ ((False ∧ p1) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41809640390545925575582018863 : (((((p2 ∧ True) ∧ p4) ∧ (((((p3 → (False → (p5 ∨ (True ∧ p5)))) ∧ p5) → (False ∧ True)) ∧ (p5 ∧ (p4 ∨ p3))) ∧ False)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695511621805127030380792714574 : ((((((p5 ∧ (((p2 → p4) ∧ p3) → p1)) ∨ p5) ∧ ((p3 ∧ p1) ∨ p5)) → ((p2 ∧ False) ∨ ((((True → p2) ∧ False) → p2) ∨ True))) ∨ p3) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38663927138990550019659432634 : ((((((p1 ∨ (p1 → True)) ∧ p1) ∧ True) ∧ ((p3 → ((False ∨ p4) → p4)) ∧ ((p1 ∨ p2) ∨ ((p3 ∨ p1) → (False ∧ False))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115759503230358610241524254891 : (((False ∨ (((p4 → False) ∨ p5) ∧ p3)) → (((p2 ∧ False) ∧ ((p4 → ((p4 → p2) ∧ (p1 → p3))) ∨ (p4 ∧ True))) ∨ True)) ∨ (False ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
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
theorem thm_5_vars_53130537319875335551956714455 : (((((p3 ∨ ((((p5 ∧ p4) ∨ p2) ∨ p4) → False)) → p4) ∧ p3) ∨ ((((p2 → p4) ∧ (p2 → p4)) → (False ∧ (True → p3))) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207534191949666555213631510157 : ((((p1 ∨ (p3 ∧ False)) ∧ p5) → p4) → ((p5 ∧ (p3 ∧ (p1 ∨ p4))) ∨ (p4 ∨ (False → (p3 ∨ (((False ∨ (p4 → p4)) → p3) ∧ p2)))))) := by
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
theorem thm_5_vars_138534536532165626007601955209 : (((((((False ∨ True) ∧ p3) → ((False ∨ p4) → p4)) ∧ (p1 → (p4 ∧ (((p4 ∨ p1) ∨ p3) ∧ p2)))) ∨ False) ∧ p4) → ((p4 → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228685424334506547489897036075 : ((p2 ∨ (p1 ∨ p3)) ∨ (((p4 ∨ p2) ∨ (p2 → (p5 ∨ ((p2 → False) → ((False → ((True ∧ True) ∨ p2)) ∨ p5))))) ∧ ((p2 ∧ False) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78924531341446732994979049042 : ((((p1 → True) → (((p4 → ((True → (True ∨ False)) → (False → (True ∨ p4)))) → (p5 → False)) ∧ ((True ∧ p2) ∧ p5))) ∧ (p4 → p1)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711257130622762089758497049574 : ((((p5 ∧ ((True ∨ (p4 → False)) → p1)) ∧ ((((True ∨ (p2 → (p2 → ((((p5 ∧ False) ∧ p1) ∨ False) ∧ p5)))) ∧ True) → p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172888018645332722460365814569 : ((p1 ∧ (p4 ∧ (True → (((p5 ∨ (False ∨ p1)) ∨ (p4 ∨ p5)) ∧ (p1 ∨ p4))))) ∨ ((p1 ∨ (((p1 ∨ True) ∨ (False → p4)) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43113229517021490016944357219 : (((((((p5 ∨ p5) ∨ (p1 ∨ ((p4 ∨ p5) ∧ p3))) ∨ ((True → p2) ∨ (p5 ∧ p4))) ∨ (((p5 → False) ∧ p4) → p1)) ∧ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157224098930828622633658030931 : (((((p4 ∨ (p1 ∧ p5)) ∧ (True → (p2 ∨ ((p4 ∨ p1) ∧ p1)))) → (True ∧ (p5 → p1))) → p2) ∨ (True ∨ ((p4 ∧ (p3 → p4)) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321165756318869363427360782563 : (p4 ∨ (p3 ∨ (((((False → p3) → False) ∧ (((((p2 ∨ p4) ∨ p2) ∧ p4) ∧ (p5 ∧ ((p4 ∨ p3) ∨ p3))) ∧ p5)) ∨ (p4 → p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671272121842313307951110857626 : ((((p5 ∨ ((((p4 → ((p3 → (p5 ∨ p4)) ∨ p4)) ∧ p3) ∧ ((False → False) → (False ∧ (p1 ∨ p1)))) ∨ False)) ∨ ((p1 ∧ p2) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615368254363400490497044735711 : (((((((p2 ∧ p2) ∨ p3) ∧ (False ∧ ((((p2 ∧ (p5 ∨ True)) → p5) ∧ p4) → p3))) ∨ ((p1 ∨ True) ∧ (False ∨ (p1 → False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_58158274002221896432844783281 : (((p3 ∧ True) ∧ ((((((p5 ∧ (((p5 ∧ True) ∨ False) → p2)) ∧ (p5 ∧ (p2 ∨ (True ∧ (p5 ∧ True))))) ∧ p2) → p2) → p3) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165632453269365335679553718542 : ((((p4 ∨ p3) ∧ (p4 ∧ (p3 ∨ p5))) ∧ (p3 ∧ ((False → (p2 → True)) ∨ (p3 ∨ p2)))) ∨ (True ∧ (True ∧ ((False ∧ (p4 → p1)) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695386361445101666973326376130 : (((((((((p3 ∨ p1) ∧ p4) → p1) ∧ True) ∨ (p5 ∧ p2)) ∧ (p2 ∨ p2)) → (False ∧ (p3 ∨ (True → (True → ((False ∨ False) → p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487858493030602760874771757262 : ((((((True ∧ False) ∨ p1) → (p1 ∧ p2)) → ((((((p5 ∨ (p4 → p3)) → p4) ∧ False) ∨ p4) → (p3 ∧ p5)) ∨ ((False ∧ True) → p2))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263563054053476819433330896455 : (True ∧ ((((p3 ∨ p1) ∧ (p4 → (((p4 → (p4 → True)) → p3) ∧ ((True ∨ p2) → True)))) → (p5 ∨ p3)) ∨ (((p2 ∧ p1) ∧ p3) ∨ True))) := by
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
theorem thm_5_vars_322365056100678301295493639192 : (p5 ∨ (((True ∨ ((p3 ∨ p1) ∧ ((p1 ∨ ((False ∧ p1) ∧ False)) ∨ ((p2 ∨ ((True → p3) → True)) → p1)))) → (p2 ∧ (p4 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66184652906530052001635606526 : ((p5 ∨ ((p5 ∨ ((p2 ∧ (p1 ∨ (((p2 ∨ ((p4 ∧ True) ∧ (True ∧ False))) → p2) ∨ p5))) → False)) ∨ (True → ((False ∧ p4) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299177158282941688576555519735 : (False ∨ (((((p1 → (p4 → ((p3 ∨ p5) ∧ (p3 ∨ (p4 → p1))))) ∧ (p3 → False)) ∧ ((True ∨ ((True ∧ False) → p3)) → p4)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65811515146169192509934589940 : ((p4 ∨ ((p2 ∧ (p1 ∨ (((p2 → True) → p1) ∨ p4))) → ((False ∧ p1) ∨ ((True ∨ p3) ∧ (((p4 → (p1 ∨ p5)) ∨ p2) → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51048149665273144590301829608 : (((p2 ∨ (p1 → ((False ∧ (p2 ∧ p5)) ∧ ((p5 ∧ (True → (p2 → p1))) → (False → p2))))) ∧ (True ∧ ((p1 ∧ True) ∧ (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117076075779796019517791825968 : (((True → p5) → (((((p5 ∨ p1) → (p2 ∧ p2)) ∧ ((p4 → p5) ∧ p4)) ∧ ((p3 ∨ (True ∨ True)) ∧ p5)) ∧ (True ∨ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319740297211162874139028430496 : (p4 ∨ (((p3 ∧ ((p1 → p5) ∨ p4)) → p1) ∨ (((False → True) ∨ ((False ∧ ((p5 ∨ p4) ∨ p2)) ∨ ((True ∨ False) → (True ∨ p5)))) ∨ False))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608240968254650727508160140107 : (((((((((((p2 ∧ False) ∧ ((((False ∧ p2) ∨ False) ∧ (True ∧ p1)) → p4)) ∧ (p4 ∧ p1)) ∧ p1) ∧ p3) ∨ True) ∨ False) ∨ False) ∨ p2) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46787768192242842418344849634 : (((p4 → (True → ((((True → ((p1 ∨ True) ∧ True)) ∨ ((False → p2) → (p2 ∨ p3))) → (p1 ∨ p3)) ∧ (p3 ∨ p3)))) ∧ (p3 ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313981787919435318074271186139 : (p3 ∨ (((p1 → (p5 → (((p2 ∨ p3) ∨ p4) ∨ p3))) → (p1 ∧ ((False ∨ (p4 → ((p4 ∨ p4) → (True → p4)))) ∨ False))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152648225085896291015202550605 : (((True → p3) ∧ (p4 ∨ ((((p1 ∨ True) → p4) → p5) → (((False → False) → p1) ∨ (p2 ∧ (True ∨ True)))))) → ((p2 → (p1 ∨ p4)) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191804332547776645052940439834 : ((p2 ∨ ((((True ∧ False) → p3) ∧ p1) → (p2 ∧ True))) ∨ ((False ∨ p5) ∨ (((False ∧ p1) → (p2 ∧ (True ∧ (p5 ∨ True)))) → (False → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207757208343020262993827007058 : (((p1 ∨ ((True ∧ True) → p5)) → p2) → ((False ∧ (((p5 ∧ ((p1 → True) → p3)) → p3) → (True ∧ p1))) ∨ (p4 ∨ ((True ∧ True) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41949884644258299818695581303 : ((((p1 ∧ p5) ∧ (((True ∧ ((((p5 ∧ p4) → p4) ∧ p4) ∨ (p1 ∧ (((p2 → p3) → (p5 → p5)) → p1)))) ∧ p3) ∧ p2)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_813692283489089820528920957246 : (((((p4 → ((((p3 ∨ p2) ∨ (p2 ∨ (p5 ∧ ((p2 → (p5 ∨ p3)) ∧ (False ∧ (p1 ∧ p2)))))) ∧ (p2 ∧ False)) ∧ p5)) ∧ p4) ∧ p4) → p1) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41099305503765888244435290007 : ((((((p2 ∧ p3) ∨ (((False ∧ p2) ∧ (p5 → (p1 ∨ p5))) → p5)) → (p4 ∧ (False ∨ (p5 ∨ p2)))) ∧ ((p1 ∨ p1) ∨ True)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305791961998534594635146032565 : (p1 ∨ (((p3 ∧ (((False ∨ p4) → p1) ∨ True)) ∧ p5) → ((p5 ∧ (p3 ∧ (p1 → (p4 ∨ p5)))) ∧ (((p5 → False) → (False ∧ p4)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h23 := h21.left
  let h24 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h25 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23
  case inr h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h23



