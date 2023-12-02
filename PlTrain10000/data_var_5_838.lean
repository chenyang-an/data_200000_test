variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610492440046053011653383355164 : ((((((p4 ∨ ((p4 ∨ (True ∨ p3)) → ((p2 → p3) → ((p5 ∨ (p5 ∨ ((p5 ∨ True) ∨ p5))) ∨ (False ∧ True))))) → p4) → p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69136033932571582661471185787 : ((p5 → (((p4 ∨ ((p4 ∧ (False ∧ (p3 ∨ (True ∧ (False → False))))) ∨ p4)) ∨ ((p2 → (p4 → p2)) ∨ True)) ∧ (True ∨ (True → p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780044940985545265243049076212 : (((p2 ∨ ((p3 ∧ (True ∧ ((p3 ∨ (((p3 ∧ (True → (p1 ∧ p3))) ∧ p1) ∧ (True ∧ ((p1 → False) → p2)))) ∨ p5))) ∨ (False → p1))) ∨ p1) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688049255660218148491789797096 : (((((((p2 → p2) → False) ∨ p4) ∧ ((p3 → True) → (p2 ∨ ((p3 ∧ True) → False)))) ∧ (((p5 ∧ (p3 ∨ p5)) ∨ (True → p2)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47640390738486163282708752261 : (((((False → ((p4 ∨ p2) ∨ ((((p4 → p3) ∨ p5) ∨ p2) ∨ (((p2 → p1) ∨ (True → p2)) ∧ p4)))) ∨ p1) ∧ p4) → (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168840706925185743237702548858 : ((p3 ∨ (((p5 ∧ (True ∨ (p1 → False))) ∧ (p2 ∧ False)) → ((p3 ∧ (False ∨ p1)) → p4))) → (((False → (p2 ∧ p4)) → False) → (False ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p2 ∧ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (False → (p2 ∧ p4)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64055629975685419294258525847 : ((False ∨ ((((((p5 ∨ False) ∨ ((p1 → p4) → p5)) ∨ ((p2 ∧ (p4 ∨ p4)) → p4)) ∨ p4) ∨ True) ∨ ((False ∧ (p2 ∨ False)) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64892918762349236354726084666 : ((p2 ∨ ((True ∧ ((p4 ∨ (p1 ∧ (p2 ∧ (((((False ∧ (True → True)) ∨ False) ∨ p5) → False) ∨ p2)))) → p4)) ∨ (False → (p3 → True)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323677779694809613694694273361 : (p5 ∨ (((p2 → False) ∨ ((p5 ∨ (p5 ∨ p1)) ∨ ((((p4 ∨ ((p3 ∧ False) → p1)) → True) ∧ p5) ∧ p2))) ∨ (False → (False → (p2 ∧ True))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207699135880290668959945816657 : (((True ∧ ((False ∧ p2) ∧ p3)) → p4) → (p1 ∨ ((p3 ∨ ((((p4 ∧ (p4 ∧ False)) ∨ p2) ∨ p2) ∧ False)) ∨ ((p3 → (p2 ∨ p1)) → True)))) := by
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
theorem thm_5_vars_140921616549852186780733147222 : (((p5 ∧ (True ∨ (p3 ∨ (((False → p3) ∨ True) ∧ p5)))) ∧ ((p3 ∧ p5) ∨ ((True → (False ∨ p2)) → (p4 → p3)))) → (True ∧ (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h29 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348008056137768229518506913232 : (p3 → ((False ∧ p4) ∨ ((p1 ∨ ((True → ((p5 ∧ False) ∧ p1)) ∧ ((p3 → p4) ∨ p3))) ∨ (((True → ((p1 ∧ p1) ∨ p5)) → p4) → True)))) := by
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
theorem thm_5_vars_205555280897119845626802622964 : (((p4 ∨ p5) ∧ ((p4 ∧ False) ∧ p4)) ∨ (((p3 ∨ ((p5 → True) ∨ (p3 ∧ p4))) ∨ ((((p1 ∧ p3) → p3) → (True → False)) ∧ p3)) ∨ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341718520970405515195594806492 : (p2 → ((((p1 ∨ (p5 ∨ (False ∨ (p5 ∧ p5)))) → p4) ∨ (((p5 ∨ p1) ∨ False) ∧ ((False → False) → (p1 ∧ (p3 ∨ p1))))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230169538924238656330207122156 : (((p5 ∧ True) ∧ p2) → (p4 ∨ ((False ∨ (p1 ∨ ((p3 ∧ (True ∨ False)) ∧ (False → (p2 → (p5 ∧ (True ∨ p1))))))) ∨ (p1 ∨ (p2 → p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119340986915637441696007891207 : ((p3 → (((False ∧ True) ∧ p3) ∨ (((p4 ∨ ((p3 ∨ (p5 ∧ (p4 ∨ (p1 → p3)))) ∨ (True ∨ p5))) ∨ (True ∧ True)) → False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213134505928097561665261614937 : ((((p3 → False) ∧ p1) ∧ p5) ∨ (((p1 ∧ ((((((p2 ∨ p3) ∧ p4) → (False → True)) → (False → True)) ∧ (p5 ∨ p2)) ∨ p1)) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348154823626713828476545905682 : (p3 → ((p5 ∧ p5) → ((p3 → (p5 ∧ ((True ∨ (((((p5 ∨ (p5 ∧ (p4 ∨ False))) ∨ p5) → p2) ∧ p3) ∨ False)) → (p4 ∨ p4)))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_993032961551726987684970113153 : (((p4 ∧ (p2 ∧ (p3 ∨ (((((True ∨ ((((p1 → (True ∧ p5)) → True) ∧ p5) ∨ p4)) → (p1 → False)) ∧ p5) ∨ (False → p4)) → False)))) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((((True ∨ ((((p1 → (True ∧ p5)) → True) ∧ p5) ∨ p4)) → (p1 → False)) ∧ p5) ∨ (False → p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246516772918391832329859622751 : ((p5 ∧ p1) ∨ ((True ∧ ((((True ∨ (p4 ∧ (p3 ∧ (p1 ∨ p2)))) → True) → (True ∨ p3)) → p3)) → (p1 → (((p3 → False) ∧ p4) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((True ∨ (p4 ∧ (p3 ∧ (p1 ∨ p2)))) → True) → (True ∨ p3)) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163071272999484761576695129815 : (((((p3 ∧ False) ∨ p3) → ((((False ∨ False) → False) → p2) → p2)) → (p2 ∨ (p2 → True))) ∧ ((((p3 ∨ p3) → p3) ∨ p2) ∨ (True ∧ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773443405578137279346825401 : (((p2 ∧ p2) ∨ ((p5 ∧ ((((p4 ∨ p2) ∨ ((p4 ∧ ((p1 ∨ p1) ∧ p3)) → (True ∨ (p3 → p3)))) ∧ p3) → p5)) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343348728898395946824716764486 : (p2 → ((p1 → p1) ∧ (((p3 ∨ ((False ∧ (((True ∨ p2) ∧ False) ∧ p3)) ∨ (((p3 ∧ p1) ∧ False) ∧ True))) ∨ (p5 ∨ True)) ∨ (p1 ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56155370112486236314337673101 : (((True ∧ ((p5 ∨ p5) ∨ p1)) ∨ (((p5 ∧ (p2 → p4)) ∨ False) ∨ (((((p5 ∨ (p4 → (p5 ∧ False))) → p5) → p2) → p1) ∨ True))) ∨ False) := by
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
theorem thm_5_vars_704477989502545814801492134251 : (((((p3 ∨ (p4 ∧ p5)) → (((p3 → p3) → p3) ∧ False)) → (((((p5 ∨ (p3 ∨ p2)) ∧ (p5 ∨ True)) ∨ (p2 ∧ p1)) → p2) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148255414315693612058685933519 : (((False ∧ (((p5 ∧ p2) → (False → (p3 ∨ (False ∨ (p3 ∧ (True ∨ p2)))))) ∧ p3)) ∨ (p3 ∧ (p3 → True))) ∨ ((p1 ∨ False) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230302075631301514057020327199 : (((p1 ∨ p2) ∧ True) → (p3 ∨ (((p4 ∨ p1) ∧ p3) → ((p2 ∨ (p1 → p5)) ∨ (True → ((p4 ∨ (p2 → p2)) ∧ (p3 → (p5 → p3)))))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- Implications on the right can always be decomposed.
      intro h16
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165765763022804846859837850436 : ((((p1 → (p5 → True)) ∧ p5) → (((((p4 → (p3 ∧ False)) ∧ True) ∨ p5) ∨ True) ∨ p3)) ∨ ((p1 ∧ p2) ∧ (((p5 ∧ False) → p4) ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_684503818213042902482173346763 : ((((((p1 ∨ p2) ∨ ((p3 → False) ∧ True)) ∨ (p1 ∨ ((True → p2) ∨ ((p5 → p3) ∨ p5)))) ∨ (p3 ∧ (((p2 ∧ True) ∨ p5) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_626656480467456721233804154309 : ((((p4 → (p2 → ((False ∧ ((p5 ∨ (p4 ∨ ((p4 → p1) ∧ (p5 ∨ p3)))) → ((p4 → (p4 → p1)) → p5))) ∨ (p4 → False)))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_62191024344775552711414866846 : ((p3 ∧ (((p4 ∨ ((p4 ∧ (p4 ∧ (p3 ∧ p5))) ∨ (p1 → ((((p1 ∧ p1) → p3) → (p3 ∨ p5)) → (p5 → p2))))) → p1) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774282342409921740514248905706 : (((False ∨ (((p1 ∨ ((((True → (False ∨ (True ∨ p2))) ∨ p4) ∧ (False ∧ p4)) → (p1 ∧ (p4 ∧ p3)))) ∨ p2) → ((False ∨ p5) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213521447254685057482695157601 : (((p5 → (p2 ∧ p3)) ∧ p4) ∨ ((p3 → p5) → ((p3 → ((p4 → p1) ∨ (True ∨ p4))) ∧ ((p3 → (p2 → False)) → (p1 → (p1 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33712952766559165879763694963 : ((p5 ∨ ((True ∧ (((((p1 ∧ p2) → (p2 ∨ (p1 ∧ (p5 ∨ (p2 ∧ False))))) → (True ∨ True)) ∧ p2) ∧ (p2 ∨ (p4 ∨ p1)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_172264887257830263041724361373 : ((((p4 ∨ (((p1 ∧ p2) ∨ p5) ∧ True)) ∨ p1) ∨ (p1 ∧ ((False → p2) → p5))) ∨ ((False ∧ p3) → ((p1 ∨ True) ∨ ((p3 ∧ p2) ∧ p2)))) := by
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
theorem thm_5_vars_703673390723755889341485493465 : ((((((p1 → ((p2 ∧ (False → p4)) → p3)) ∨ True) ∧ p4) → ((((p1 → (p2 → p5)) ∨ ((False ∧ True) → (True ∧ p4))) → p3) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49377578917476239546374006928 : (((p5 → (p5 ∧ (p1 → (((True ∨ (False ∧ p5)) → (p2 ∨ (p4 ∨ (((p4 ∧ p3) ∧ False) ∨ p2)))) ∨ p5)))) ∨ ((False ∧ False) → p3)) ∨ p3) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51229404689047680154028166575 : (((((p2 → p2) ∧ (p5 ∧ p2)) ∨ ((p4 ∧ (p2 ∨ ((True ∧ p4) → p2))) ∨ (p3 ∧ p4))) ∨ (p1 → (False ∨ (p4 → (False ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338421323435034046562775243510 : (p1 → ((p4 ∧ ((p5 ∨ p1) ∧ True)) → (((p5 ∨ p2) ∧ (p2 → (False ∨ ((p2 → False) ∧ (p2 ∨ (p4 ∧ p5)))))) ∨ ((True ∨ True) ∨ False)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171934486165726493467009094627 : ((((p4 ∨ (p5 ∧ (p3 ∧ ((p5 ∧ (p2 ∧ p2)) → True)))) ∨ True) ∧ (p3 ∨ False)) ∨ (p2 → ((True ∨ ((True ∧ (p2 ∧ p1)) ∨ False)) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258816633010991793877388771861 : ((True → False) → (p5 → ((((((p5 → False) ∧ True) ∨ (p1 → (p1 → p5))) → (((p2 ∧ p2) ∧ p1) ∧ p5)) ∧ (p4 ∨ (p2 ∧ p3))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874734103441130140570751751579 : (((((p4 ∧ (True ∧ ((p4 ∨ (p4 ∧ (p1 → p2))) ∨ (((p2 ∨ (((False → p5) → p1) → p4)) → True) ∧ p1)))) ∧ p2) ∧ (p3 → p4)) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340939003374198811454947327820 : (p2 → (((p1 → (p4 ∨ (p4 ∧ p4))) ∨ ((((p1 ∧ p1) ∧ ((False ∧ (True → p4)) → True)) ∨ (p5 ∨ p3)) ∧ (p4 → (p1 ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696259288496622713176425862821 : ((((True → (((p3 → False) ∧ ((p1 ∨ p4) ∧ (p5 → p2))) ∧ (p1 ∧ True))) → ((p4 → True) → ((p4 ∨ True) → ((False ∨ p3) ∨ p1)))) ∨ p2) ∧ True) := by
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
  cases h3
  case inl h4 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328978349634916553616310335203 : (True → (((True → ((p2 ∨ False) → p3)) ∧ p4) ∨ ((False → ((p5 ∨ p4) → p2)) → ((False → (p3 → p2)) → ((p3 ∨ (p4 ∨ True)) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67921872596079448976662057264 : ((p2 → ((p1 ∨ (p2 → ((((p5 ∧ p2) ∨ True) → True) ∧ p5))) ∧ (((p5 ∨ ((p3 ∧ False) ∧ p5)) ∧ p3) ∨ ((p2 → p1) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314440382117781238957134784991 : (p3 ∨ ((p3 ∨ (((True ∧ (p3 ∨ (((p3 ∧ p5) ∨ (p3 ∧ p4)) ∧ (p3 ∨ True)))) ∧ False) ∧ (False ∨ True))) ∨ (True ∨ (p1 ∧ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51207513636161900826466724528 : ((((((p1 ∧ p5) → p3) ∧ ((p5 ∧ False) ∧ p3)) ∧ ((p5 → (p1 ∧ (p4 ∧ True))) → p3)) ∨ ((p4 ∨ p2) ∧ (True ∨ (p5 ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157668756782912660770339602841 : ((((p3 ∧ ((p2 → (p1 ∧ p3)) → True)) ∧ (p3 ∧ (p5 ∧ (p5 ∧ False)))) ∨ ((True ∧ True) ∨ p2)) ∨ (p3 → (p1 ∨ (p5 → (p2 ∨ p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_612909254251740839889626585357 : (((((p3 ∨ (((p2 ∧ True) ∧ (True ∧ (((p3 ∨ p2) ∨ p4) ∧ ((p1 ∧ p5) ∧ (p4 ∨ (p5 ∨ False)))))) ∧ False)) ∨ (p4 ∧ p1)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40856888395983270676973935601 : ((((((p1 → (p4 → ((p2 ∨ ((p1 ∧ p5) ∧ (True → (p2 ∨ p2)))) ∧ ((p4 → p2) ∨ p3)))) ∨ p3) ∨ p4) ∧ (p5 ∨ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_23824599865650823962886215437 : (((p4 ∧ ((p1 ∧ True) ∨ p1)) ∨ ((((((p1 ∧ p2) → ((((p1 → True) ∨ p4) ∧ p2) ∨ p5)) ∨ p2) → (p1 ∨ False)) ∨ True) ∧ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_3045416265011781323757072720 : ((True → (p4 → True)) → ((False ∨ ((p2 ∨ (((((True ∨ (True → p3)) ∨ p5) → p2) ∧ False) ∨ (p2 ∧ (p4 → p4)))) ∨ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37328872451798414134685814644 : ((((((((((False → (p4 ∨ p2)) → False) → (p5 ∨ (p5 ∧ ((p2 ∧ p4) ∨ True)))) → True) → True) ∧ (p5 ∨ p1)) ∧ p5) ∨ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622266840004474774273508674106 : ((((p3 ∧ (((((((p3 → p2) ∧ p4) ∨ (p2 ∧ (p4 ∧ ((p2 → p3) ∨ p4)))) ∨ ((p2 ∨ False) ∧ False)) → True) → p3) ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203582860866089071073406792671 : ((p1 ∨ (False → (p4 ∧ (p2 → p5)))) ∧ ((p4 ∧ ((p5 ∨ p5) → (True ∧ (p2 ∨ p2)))) → ((False ∨ True) ∧ (((p5 → p4) ∨ p3) → p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304085824346745992156942688548 : (p1 ∨ ((p5 ∨ ((p1 → (((((p2 ∨ False) ∨ (False ∧ (True ∧ ((False ∧ (p4 ∨ p1)) → p4)))) ∨ (p1 ∧ p2)) ∧ p2) ∨ p3)) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336188813708548867036227050948 : (p1 → (((((p2 ∨ ((((p3 ∨ p1) → p3) ∨ True) ∨ p5)) ∨ p3) ∧ (p2 ∧ (p1 → (p2 → (p2 ∨ (p5 ∨ False)))))) ∧ (p2 ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776851964469216643151995600666 : (((p1 ∨ (((p5 ∨ False) → (p4 ∧ ((p5 → ((p1 ∧ p1) ∧ ((False ∧ ((p1 → (p4 ∨ p1)) ∨ p2)) ∧ (p4 ∧ True)))) → p4))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256963072138706949268923226252 : ((p1 ∨ p5) → ((((p3 ∨ (((p5 → p5) → p1) ∧ p1)) ∨ p2) ∨ ((True ∨ p2) ∨ True)) ∨ (False ∨ (p5 → (p4 ∨ ((True → p3) ∨ p2)))))) := by
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
theorem thm_5_vars_322356795066241740998340820181 : (p5 ∨ ((((p1 ∧ (p2 ∨ (False ∧ ((p2 ∧ p1) → p3)))) ∧ (p4 → (p3 → (True ∨ ((p2 → p2) ∨ p1))))) ∨ ((p5 ∨ False) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_7265356073779503918553037129 : (((p2 ∨ (p3 → (((((p1 ∧ p2) ∧ p1) ∧ p5) ∨ (((True → (p2 → False)) ∨ True) ∧ (p3 ∧ p3))) ∨ ((p1 → p2) ∧ p2)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42609942069953375726402150301 : (((p3 ∨ (((p2 ∧ p4) ∨ (p4 ∧ (((p1 → (p3 ∨ p1)) → (p4 → False)) → ((False ∨ (p4 → p1)) ∧ (p2 → p2))))) ∨ False)) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217489253800518828672501410293 : ((((p5 ∧ p2) ∧ p5) → p3) → ((((p3 ∨ (p3 → ((p4 ∨ ((p4 → ((False ∨ True) ∧ (p5 → p5))) → p5)) → p1))) → True) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ (p3 → ((p4 ∨ ((p4 → ((False ∨ True) ∧ (p5 → p5))) → p5)) → p1))) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205290243089663413261936243193 : (((p2 ∧ (p5 ∨ p1)) ∨ (p3 ∧ p3)) ∨ (((((True ∧ p4) ∧ (((((p4 ∧ (p5 ∧ p2)) ∨ p5) ∧ True) ∨ True) ∨ p5)) ∧ p2) → p4) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37265944646757743818221927278 : ((((p4 ∧ (p4 ∨ (p1 ∨ ((p3 ∧ (p5 ∨ (False ∨ (((((True ∧ p5) ∧ p2) ∨ False) ∧ p4) ∧ p2)))) ∨ (p4 → p3))))) ∧ True) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225337269917947499932162070928 : (((p1 ∨ p1) ∧ False) ∨ (((p1 ∧ (p3 ∨ p4)) ∨ (p3 ∨ ((False ∧ (False ∧ ((p1 ∧ p1) → p4))) → (p4 ∧ False)))) ∨ ((p3 ∨ p4) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116124898997059656557876277864 : (((True ∧ (p5 → True)) ∧ ((p1 → ((p2 ∨ (((p1 ∨ (p2 ∧ (True → False))) ∧ p5) ∧ (p5 → p4))) ∧ (p4 → p4))) → p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602853578285682916255616252658 : ((((p1 ∨ ((False ∧ ((p5 ∨ p3) → ((p1 ∨ ((((p4 ∨ p4) ∨ (True ∧ p2)) ∧ p2) ∨ (p2 ∨ True))) ∧ (p1 → True)))) ∨ p4)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48938556845228206122201701696 : ((((((p3 ∨ (p3 ∨ p5)) → (p3 → p5)) ∧ (((p3 ∧ (p4 ∨ p5)) ∨ p4) ∨ ((True ∨ p2) ∧ p3))) ∧ p5) ∨ (p4 → (p4 ∨ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353653076835720602770913055082 : (p4 → (p5 ∨ (((((p1 ∧ (((p4 → p1) → p4) → ((p3 ∧ (p1 ∧ p4)) ∧ (p2 → p3)))) → p1) ∧ ((p2 ∨ p5) ∧ p2)) ∨ p5) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190701667174907413186101463806 : (((((p4 → p2) → (p3 ∧ False)) ∨ p4) ∧ (False → True)) ∨ ((((p2 ∧ p4) ∨ p3) → (p1 ∨ (p3 ∨ ((p3 → p4) ∨ True)))) → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591978782338872125505025873911 : ((((((p5 ∨ p1) ∨ ((p1 ∧ p3) ∨ (((((False ∨ False) → (True → p5)) ∧ p1) ∧ (True → (True → p2))) ∧ p4))) ∨ (p5 ∨ False)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197974944378832676769659275304 : (((p1 ∨ True) ∧ (False ∨ ((p4 ∨ False) ∨ p5))) ∨ (p3 → (((((p5 → True) → False) ∨ p3) ∧ (p5 → ((False → p4) → p3))) ∨ (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52112147863066007223413099781 : ((((((((False ∨ p5) ∧ (p5 ∨ p4)) ∨ p4) → (p1 ∨ (p2 ∧ p3))) → p1) → p4) → (p1 → ((((p1 ∧ p4) → p1) → p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316991888223003614579929822908 : (p3 ∨ (p3 → (((p2 → (True ∧ (True ∧ p5))) ∧ (p1 ∧ (((p5 ∧ p5) ∧ p1) → ((True ∨ p3) ∨ p5)))) → (p1 → ((True → p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67547562936275993207606790856 : ((p1 → ((False ∨ (p5 ∧ p5)) ∨ (((((((True → (False ∨ (p1 → True))) ∧ p5) → False) ∨ False) → (False → p1)) → False) ∧ (True ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300445622542956934031013099291 : (False ∨ (((p4 ∨ ((False ∨ (p1 ∨ (p3 ∨ (((p1 → p4) ∧ p3) ∨ True)))) ∧ p4)) ∧ (p5 ∧ ((p5 → p1) ∧ p1))) → ((p3 ∧ p3) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h3.left
        let h16 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h3.left
          let h22 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Conjunctions on the left can always be decomposed.
            let h27 := h26.left
            let h28 := h26.right
            -- Conjunctions on the left can always be decomposed.
            let h29 := h3.left
            let h30 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h33 =>
            -- Conjunctions on the left can always be decomposed.
            let h34 := h3.left
            let h35 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327790895044730308454180250008 : (True → (((((p1 ∨ (p2 ∨ (p1 → ((p1 → p2) → (p3 → (p4 ∨ ((p1 ∧ p1) → False))))))) → False) ∧ (p1 → p3)) ∧ p2) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214140474173347779001720784766 : ((((p4 → True) ∨ False) → False) ∨ (p4 ∨ ((False ∧ p4) ∨ (p3 → ((False ∨ ((p1 ∨ (p4 ∧ ((False ∧ p5) ∨ p2))) → p3)) ∧ (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Implications on the right can always be decomposed.
  intro h11
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40824280647390908044287845354 : ((((True → (((p1 → (p2 → (p2 ∨ p5))) → (p3 ∨ ((p5 → p4) ∧ p1))) → (False ∧ (((p1 ∧ p1) ∨ p3) ∨ p4)))) → p4) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233227912998376194351123805280 : ((p5 ∧ (p4 → p2)) → (((((p2 → ((p3 → True) ∨ (False → p3))) ∧ (p3 ∨ p1)) → p3) ∧ (((True ∨ (True → False)) → False) ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114328557461474032814759355256 : ((((p3 → p4) → (p4 ∧ (((p2 → (p3 → p4)) ∧ (((p5 ∧ p3) → p4) ∨ p3)) ∧ p4))) ∧ (((p1 ∨ p2) ∧ p5) ∨ p4)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663460564720458013050069669477 : (((((p5 ∨ p3) → (((p5 → (p3 ∨ (p3 ∧ ((p1 ∨ True) ∧ (p4 ∧ p3))))) ∨ (False ∨ (p4 ∧ p5))) ∨ (p1 ∧ True))) → (False ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677376090659461491786689551483 : (((((((p5 → p1) ∧ (False ∧ (((p2 ∨ (p1 ∧ (False → False))) ∧ (p5 ∨ False)) → False))) ∧ p2) ∨ True) ∨ (p5 → ((p1 → p3) ∧ False))) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_210582297798614397923209138364 : ((((p1 → p2) ∧ p2) → True) ∧ ((p2 ∨ (((p2 → (((p3 → p5) ∧ p3) ∨ p5)) ∨ (False ∧ (p3 → p5))) → (p5 → p2))) ∨ (p4 → True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317685798708294149805182471338 : (p4 ∨ (((p2 ∨ (((p5 ∧ ((p4 ∧ ((p4 ∨ p4) ∨ (p1 ∨ False))) ∨ False)) ∨ (p4 ∨ ((p5 ∧ True) → True))) → (p2 → p5))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686868137440152286179468968907 : ((((True ∨ (((True → p5) ∨ ((True ∧ p1) → ((p4 ∧ (True → (p3 → p1))) ∧ False))) ∨ False)) → ((False ∨ (p5 ∨ (p2 → True))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208310404378409136273734267374 : (((True → True) ∧ (p4 → (p3 ∨ p2))) → ((((p4 ∨ p2) → (p3 → p2)) ∨ ((p2 → (((p4 ∧ True) → True) → True)) ∨ (True ∧ p2))) ∨ True)) := by
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
theorem thm_5_vars_657667985545257498752967600448 : (((((p4 ∨ p4) → ((p4 ∧ ((p3 ∨ p2) → ((p2 → (p3 → p5)) ∨ (p1 ∨ ((False → (False → False)) → p1))))) ∨ True)) ∨ (p4 ∧ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_349974953440302454199443986667 : (p4 → (((((p2 ∧ (p3 ∨ (((((p5 → p2) ∧ p5) ∨ True) ∨ p2) ∧ ((True → False) ∧ (True ∨ (p3 → p2)))))) → p3) ∧ False) ∨ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133906551246870868938545944566 : (((p2 ∨ (((p4 → ((p5 ∨ p1) ∧ p3)) ∧ (((p1 ∨ (p1 → p1)) ∨ (p5 ∨ p2)) ∧ p1)) → (p2 ∧ p5))) ∧ p4) ∨ ((True → p2) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346764467619998545669260070772 : (p3 → (((p1 ∧ (((((False → (True ∨ (p5 ∨ p5))) ∧ p1) → (p4 → p5)) ∨ p4) ∨ (True ∧ p4))) ∧ p2) ∨ ((p4 ∧ p3) ∨ (False → p3)))) := by
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
theorem thm_5_vars_243027218807342324968672712363 : ((p4 → True) ∧ (p5 → ((((p2 ∨ True) → (p4 ∨ (p3 → (p5 → p5)))) → p3) → ((False → False) ∧ ((p5 ∨ (p2 ∧ (p5 → p3))) → p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : ((p2 ∨ True) → (p4 ∨ (p3 → (p5 → p5)))) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- One of the premise coincides with the conclusion.
        exact h14
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h15 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112927707558946992060891541395 : ((((p4 ∧ True) → (p1 ∨ (((((((p2 → False) ∨ p3) ∧ p5) ∨ p2) ∧ (p5 ∨ (p3 → p2))) ∧ p4) → (p5 ∧ p5)))) → p5) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219963621284515994679807175845 : ((p5 → ((True → p3) ∨ False)) → (((False ∧ p1) ∨ ((((p4 ∨ p1) ∨ p2) → True) → (False ∨ (p5 ∧ True)))) ∨ (p3 ∨ (p5 → (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702781312339998747959272043770 : (((((True ∨ (((False ∨ False) → True) ∧ p2)) → (p3 → p4)) ∨ (((p4 → (p1 ∧ p2)) ∨ p2) ∨ (((True ∨ True) ∧ (False → p3)) ∧ True))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149220162723836268640386342161 : (((p2 ∧ p2) ∨ (((p3 ∨ p1) ∨ (p3 ∧ p5)) ∨ (True ∨ (p5 ∨ (p5 ∧ (False → ((True ∧ p1) ∨ p2))))))) ∨ (False ∧ ((p2 ∧ False) → True))) := by
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
theorem thm_5_vars_51205998591190105761007940022 : ((((p4 → ((False ∨ (p3 ∧ (p1 ∧ (p1 ∧ p3)))) ∧ p4)) → ((p2 → (p5 → p5)) → p2)) ∨ (p1 → (False ∨ ((p4 ∧ False) → p1)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619521443266977939972826467730 : (((((p3 → (p3 ∨ p4)) → (((((p2 ∧ ((True ∧ p5) → ((False ∧ (p1 ∨ p3)) → p4))) → p1) → p1) ∨ False) ∨ (False → False))) ∨ p1) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



