variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258332047232640507865491641175 : ((p5 ∨ False) → (((((p2 ∧ ((p4 → (p5 ∧ False)) ∧ p3)) ∨ (((p4 ∨ (p1 ∨ False)) ∧ (p5 ∧ (p4 → p2))) → p4)) ∧ p4) ∨ p5) ∧ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247783850804046530732654538538 : ((p1 ∨ p1) ∨ ((((p1 ∧ (p1 → True)) ∧ p3) ∧ (p3 ∧ ((True ∧ ((p1 → p5) → p3)) → (p5 ∧ (True ∧ (p1 → p3)))))) ∨ (True ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347970014484354523859883574317 : (p3 → ((p1 → True) ∧ (((((((p2 ∨ p1) ∧ p5) ∧ ((((p2 → (p3 ∧ False)) ∨ p1) ∨ p4) ∧ p5)) ∨ True) ∧ p1) ∨ (p3 ∧ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181042422975090902745666611150 : (((p5 → p5) ∨ ((True ∨ (p4 ∧ (p1 ∧ (True ∧ (p3 ∨ p4))))) ∨ True)) → (((p3 ∨ True) → (False ∧ ((p4 → p4) ∨ (p1 ∧ p1)))) ∨ True)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219953614762898436146514640102 : ((p5 → ((p1 → p2) ∧ p4)) → ((p2 ∨ (((p4 → ((p2 → ((((False ∧ True) → p1) ∨ p2) ∨ (p4 ∨ p5))) → False)) ∨ p2) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_186494079441664984730365386385 : (((p2 ∧ ((p3 ∧ p3) → (True → (p4 ∨ p2)))) ∧ (p2 ∧ True)) → ((((p2 ∨ True) → p3) ∧ p2) ∨ ((p5 ∨ p4) → ((p5 → p2) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h12
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197971443676153412799897406274 : (((False ∨ p1) ∧ ((False → (p2 → True)) ∨ False)) ∨ ((((False ∧ False) ∨ (((p1 → False) ∨ True) ∧ (p5 → (p3 ∨ True)))) ∨ (p3 ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248381438502830958684662705738 : ((p2 ∨ p4) ∨ (((p4 ∨ p1) → ((p2 ∨ (p5 → (p2 ∧ ((p2 ∧ True) ∧ (True → p5))))) → (p4 ∧ (((p5 ∧ p2) → True) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114402888706250762977592760854 : ((((((p2 ∧ (p2 ∧ True)) ∨ True) → p5) ∧ (p1 ∧ (p1 → (False ∨ (p3 ∨ (p5 ∨ p2)))))) ∨ ((p2 ∧ True) ∨ (True ∨ p5))) ∨ (p1 ∧ p4)) := by
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
theorem thm_5_vars_49265722125918657301233137276 : (((p1 ∧ (p2 ∨ (((p2 ∧ (p4 → False)) → (p3 ∧ (p5 → ((p1 ∨ p1) ∨ (p5 ∨ (p4 → p5)))))) ∨ p5))) ∨ ((True → p1) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323562495901832560854266948884 : (p5 ∨ (((((p4 → ((False → (p2 → p2)) ∨ p5)) ∨ (p4 ∨ False)) ∧ p4) ∧ ((False → p2) → (True ∧ (False ∧ p5)))) → ((True → p2) ∨ False))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h7
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h16 := h3 h14
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114220845844420412873919496895 : ((((p2 → p2) ∨ (((False → ((False ∨ (False ∧ ((p3 ∧ (p3 ∧ p4)) ∨ p4))) → p4)) ∨ True) ∨ p3)) → ((p2 ∧ p1) ∨ False)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181420893289680057716631168579 : ((p2 ∨ (p4 ∧ ((((p5 ∧ True) → p5) ∧ p3) ∧ ((p3 → p2) ∧ True)))) → ((((p1 → p3) ∨ (p4 ∧ (p5 ∨ (p1 ∧ p2)))) → p2) ∨ p2)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336075369474797366898601946306 : (p1 → (((((p4 → p2) ∨ ((((p4 ∧ p3) → p1) → True) ∧ (((p1 ∧ ((p4 ∨ p1) ∧ (p2 → False))) → p1) ∨ True))) → p2) ∧ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37195108108596799168423040537 : ((((((p4 ∧ p4) → (p5 → (p1 ∧ p3))) ∧ (((((p5 ∨ (p5 ∨ (p1 ∨ p4))) → p2) ∨ (p4 ∨ p5)) ∧ p2) → False)) ∧ p2) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693012274125483088484961919008 : (((((p3 → p1) → (((p2 → (True ∧ p3)) ∨ (p3 ∨ p5)) ∧ (True ∨ False))) ∧ ((p2 ∧ False) ∧ ((False → (False ∧ (False ∨ False))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55806404228490800407091829785 : ((((False ∧ p2) → (p2 → p4)) ∧ ((((False → (p2 ∧ p3)) ∧ p3) ∧ ((p1 ∧ (True ∧ p4)) ∨ ((p3 ∨ p3) ∧ (p1 ∧ p3)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304708319395475567930171500174 : (p1 ∨ (((p5 ∨ (((p5 ∧ (True ∨ p2)) → (((p2 → p3) ∧ (p2 ∨ False)) ∧ p1)) ∨ ((p4 → p3) ∨ True))) ∧ (False ∨ p2)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264784381041774436539948801254 : (True ∧ ((True ∧ False) ∨ (((False ∨ True) ∨ ((((False ∧ False) → p1) ∨ p3) ∧ False)) ∧ (p5 ∨ ((p1 ∧ p3) ∨ (((False ∨ True) ∨ p2) ∨ p4)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_327890641157283543154607057385 : (True → ((p3 ∨ (((((((False ∧ (False ∨ p5)) ∧ (p2 ∨ p4)) ∧ (p3 ∨ True)) ∨ True) ∧ p4) → p3) ∨ (p3 ∧ (p2 ∧ p1)))) ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85095290969763571364069491714 : ((((((p2 ∧ p5) → ((p5 ∨ p2) ∨ (p5 ∨ (p4 ∧ p1)))) ∨ p2) ∨ True) → (((p5 ∧ (p1 → p3)) ∧ (p5 ∧ False)) ∧ (p2 → p1))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p2 ∧ p5) → ((p5 ∨ p2) ∨ (p5 ∨ (p4 ∧ p1)))) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136095802176261624318548816224 : ((((p5 ∧ (((p2 ∨ p3) ∧ False) ∨ p2)) ∨ p5) ∨ ((True → p3) ∧ ((p5 → (p2 ∧ p5)) ∧ (False ∨ (True → p4))))) ∨ ((False → p5) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118547077802033202044302813399 : ((p3 ∨ (p4 ∨ ((p2 ∨ (False ∨ (p5 ∧ False))) ∨ ((p3 ∧ (((p1 ∨ p4) ∨ p3) ∨ p3)) ∨ ((False ∧ True) → (p1 → p1)))))) ∨ (p3 ∧ p4)) := by
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
theorem thm_5_vars_149503306739521538260787610924 : ((p1 ∧ (((p3 ∨ (p2 ∨ p3)) → (p2 → ((p1 → (p2 → p4)) → (p4 → False)))) ∨ (False → (False ∨ p1)))) ∨ ((p1 → (p4 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262154540244894921286115520641 : (True ∧ ((((((True → p1) ∨ p1) ∨ (((p4 ∨ p2) ∨ (p3 ∨ p4)) → True)) ∧ ((True → (p2 ∧ ((p1 → p3) ∧ p5))) ∧ p3)) ∨ False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52256467494654338695640309477 : (((p2 ∨ ((p5 → p4) ∨ ((True ∧ (p4 ∨ ((p1 ∧ p3) ∨ (p5 ∧ p4)))) ∧ p2))) → (p1 ∨ ((p1 → (p1 → (p1 → p2))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171409459940153391717901304364 : (((((False → p2) → p4) ∧ (p4 → (p2 ∧ ((p2 ∧ True) → (p1 ∧ False))))) ∧ True) ∨ (p5 → ((p1 ∧ ((p4 ∧ True) ∨ True)) → (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230388632844667935378015720672 : (((p3 ∨ p3) ∧ p2) → (((True ∨ True) ∧ p3) → (((p4 ∨ (((p1 → (p1 ∧ True)) ∧ False) ∨ (True → ((p2 → p1) → p5)))) ∨ False) ∨ p2))) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116636723789217908074310144635 : (((p2 → True) ∧ (((p2 ∧ (True ∨ False)) → ((((p2 → p1) → ((p4 → p1) → p3)) → (p1 → (p1 → False))) ∨ p4)) → p4)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690930348985134635710563853980 : ((((((p2 → (p2 ∨ (False ∨ ((False ∧ p3) ∨ p2)))) ∨ (p5 → p1)) ∨ (p4 → False)) → (p5 ∧ ((p2 → (p1 ∨ (p1 ∧ p2))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317801846161861862567048574342 : (p4 ∨ ((((True ∨ (((p4 ∨ p1) → p3) ∧ p1)) ∨ True) → (((False ∨ (True ∨ True)) → (p4 ∨ ((True ∧ (p4 → p2)) → p2))) ∨ True)) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_48918876333864667829789078100 : (((((True ∧ (p3 ∨ (((True ∨ ((p2 ∨ (p4 ∧ p4)) ∧ p2)) → False) ∨ (p1 ∨ (p5 ∨ False))))) ∧ p4) ∧ p1) ∨ ((p2 → p1) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107917512402705196139026118954 : (((True → p5) ∨ ((((p1 ∨ p5) → p1) ∨ (((((False ∨ p2) ∧ p3) ∨ (p1 ∧ p2)) ∧ True) ∨ False)) ∨ ((p2 → p2) ∨ p5))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634486240616590435911887318423 : ((((((False → (((((True ∨ p2) → (False → p4)) ∨ p4) ∨ p1) → p2)) ∨ (p5 → ((p5 ∨ False) → True))) ∧ (p1 ∨ (True ∨ p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199234745658650501869237581509 : (((False → (((p4 ∨ False) ∨ p3) ∧ True)) ∧ p3) → ((((p2 → (p4 ∧ (p5 → p3))) → p1) ∨ True) ∨ ((False ∧ p3) ∨ (False ∧ (p4 ∧ p4))))) := by
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
theorem thm_5_vars_327792933196081316262831160783 : (True → (((((True ∧ ((True ∧ ((p4 ∨ p2) ∨ False)) → p4)) ∨ p2) ∧ (((False ∨ (p5 → p3)) → (False ∧ True)) ∧ p2)) ∧ p1) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232469263192204713142416220188 : ((True ∧ (p2 ∨ p2)) → (True ∧ (((p3 ∧ (((False ∧ ((p1 → (p1 ∨ p3)) ∨ (p3 ∨ False))) ∧ True) ∧ (p4 ∨ p2))) ∨ (p3 ∨ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_336372653571180583773005392425 : (p1 → ((True ∧ (((True ∨ ((p3 ∨ ((False ∨ (True → p3)) → (((p5 ∧ p4) ∧ p3) → (p2 ∧ (p3 ∨ p5))))) ∧ p5)) → p3) ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232721227726721518750662607775 : ((p1 ∧ (p5 ∨ p1)) → (((p4 ∨ (p3 ∧ (False ∨ p4))) ∧ (True ∧ ((p5 ∧ False) ∧ (((p4 ∨ p3) → p4) ∧ p3)))) ∨ (False → (p2 ∧ p3)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h5
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h7
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705882520889287525954750544454 : ((((((p4 ∧ p2) ∧ p5) ∨ (p4 → (p5 ∧ p2))) ∧ (p4 → (p4 ∨ (False → (((((p5 ∧ (p3 ∧ p3)) ∧ p2) ∨ p4) → True) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358114888090437698538493550647 : (p5 → (p2 ∨ (((p3 ∨ ((((p4 → ((p5 ∧ (p1 ∨ False)) ∧ p4)) → True) ∨ p2) → p3)) ∨ p2) → ((p3 ∧ ((p3 ∨ True) ∧ False)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
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
theorem thm_5_vars_110971929141649290862041270795 : (((((((p4 ∨ True) ∨ (((p3 ∧ p1) → p5) → p2)) → (p2 ∧ (p1 → (False → (p1 ∨ False))))) ∧ p4) → (p1 ∨ p5)) ∧ p1) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148623078923122680854005031245 : (((((False → p2) ∨ p2) → (((p2 ∧ p1) ∧ p1) ∨ p4)) → (p3 → ((((p1 → p1) → True) ∨ p1) → p4))) ∨ (p4 → (p4 ∨ (p1 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327048009139535596349609540689 : (True → ((((p3 → ((False → p2) ∧ (False → p5))) ∨ p1) → (p2 → (p1 ∨ (p3 → (((False → ((False ∧ True) ∨ p1)) → p5) → p2))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792884390368628099507129575033 : (((True → ((p3 ∧ (True ∨ p1)) → (((p5 ∧ (p4 ∧ p1)) ∧ ((True → p4) ∨ p5)) ∨ ((False ∧ (p1 ∧ (p2 → (p4 → p3)))) → p5)))) ∨ False) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68208243114139553055554592795 : ((p3 → ((p1 → ((True → (False → (((True ∧ p2) ∧ (((p3 ∨ p4) ∧ p2) → (True ∧ p4))) ∧ False))) → ((p5 → p4) ∨ p1))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658718773739450564865571682773 : ((((p4 ∨ (p1 ∨ (((p2 ∨ False) → (((p2 → p1) ∨ (((p5 ∨ p1) ∨ False) → (p1 ∧ p2))) ∧ (p4 ∧ p3))) → p4))) ∨ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719528139268089736100396226976 : ((((p3 ∨ ((p5 ∧ p1) ∨ p4)) ∨ (((p1 ∧ ((p2 ∧ p1) ∨ p1)) ∨ (p1 ∧ ((False → (True ∧ p5)) ∧ ((True → False) ∧ p5)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55089156231877827847209727433 : (((p1 → (p4 → ((p1 → p5) ∨ p1))) ∧ (True ∧ ((p2 ∨ (p4 ∨ p4)) ∨ (p3 → (p1 → ((p2 ∧ p4) ∨ (p3 ∨ (False ∨ True)))))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158641673474357953377019142666 : ((p1 ∧ ((((((p1 ∨ (p2 → (p3 → (False ∨ p3)))) → False) → p3) → p5) → p5) → (p4 → p5))) ∨ (p1 → ((p1 ∨ (p3 → p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117955490562358537639288583398 : ((p5 ∧ (p3 ∨ (p1 ∨ ((p1 ∨ (p5 → ((p4 → ((False → (p5 ∧ False)) ∨ p1)) ∨ ((p3 ∨ p5) ∧ (p5 → p4))))) ∧ False)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200778634901229964330919894223 : ((p4 ∧ ((True ∧ p1) → (p1 → (p2 ∨ p1)))) → (((p5 → True) ∧ (p2 → ((False ∧ (p4 → p1)) ∨ ((p1 ∧ (False ∨ p5)) → p2)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191580240618453666676535163611 : ((p2 ∧ ((p5 ∨ (p5 → False)) ∨ ((p1 ∨ p2) ∧ False))) ∨ ((p2 ∧ (p3 ∧ p4)) → ((p2 ∨ (p2 ∧ False)) ∨ (p5 ∨ (True ∨ (p2 ∨ p5)))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324163497659157250567743804653 : (p5 ∨ ((((((p4 → p1) ∧ p2) ∧ (p1 ∧ p2)) ∨ p3) → False) ∨ ((((p3 → p2) ∧ p4) ∨ ((p3 → True) ∧ (p3 → (p2 ∧ False)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147843431289907253677413459939 : (((p4 ∨ (((p2 ∧ ((p2 → p1) ∨ p4)) ∨ (((False ∧ True) ∨ p4) ∨ (p5 ∨ p2))) ∨ (p3 → p4))) → False) ∨ (False → (False → (p4 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136301333574358266758693165563 : (((p5 → (((p4 ∨ True) ∨ True) → p1)) → (((False ∨ True) ∨ ((p2 ∧ (p1 → p1)) ∨ (p3 ∨ p3))) → (p3 → False))) ∨ ((p1 ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323779208817825016189627406223 : (p5 ∨ ((((p3 ∧ p4) → (((p1 ∨ (((p4 ∧ p1) → p3) ∧ (p5 ∨ p5))) ∧ p1) ∧ True)) ∧ p5) ∨ (p4 → (True ∨ (False → (p2 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670070735947361799465785032166 : ((((((p5 ∧ p4) → (((p3 ∧ p2) ∧ p2) ∧ p4)) → (p5 ∧ ((False → ((True ∧ (p5 → p1)) → True)) ∨ True))) ∨ (True ∨ (p3 → p3))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_67496831530109853720012560971 : ((p1 → ((p3 ∨ ((p2 ∨ (p4 ∧ (False ∧ p5))) ∨ (False → False))) ∧ (((True ∧ (p1 → (p4 ∧ (p1 → p1)))) → (p4 ∨ True)) ∧ p1))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176462725010318693496060300924 : (((((p4 ∨ p1) ∧ ((p5 → p5) → p5)) ∧ p1) → (p5 ∨ (p1 → p2))) ∧ ((((p3 ∧ (False ∨ (p5 → p5))) → p4) → p4) ∨ (True ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : (p5 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317833841837150974213991119616 : (p4 ∨ (((True → (p2 ∨ p5)) ∧ ((False ∨ ((p3 ∨ p3) → (p4 ∨ p5))) → (((((True → False) ∧ p4) ∧ (p4 ∧ p1)) → p3) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336186955947125243092132201049 : (p1 → ((((p4 ∨ (p4 ∨ (((((False ∨ True) ∧ p1) → ((p5 ∨ p2) → (p4 ∨ p2))) ∧ False) ∧ False))) ∧ (p3 ∨ p4)) ∧ (p3 ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149008425018807295359197126607 : ((((p4 ∨ p4) ∧ p4) ∨ ((p5 ∨ (p4 ∨ p4)) ∧ ((((False → p1) ∧ p3) ∧ p2) ∧ ((True → p2) ∨ p2)))) ∨ (p3 ∨ ((False ∧ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_136410863833491277336021027473 : (((((True → True) ∧ p2) ∧ p2) → (p3 ∨ ((p1 → ((False ∨ (p2 → ((False ∨ (p2 ∨ p3)) → p4))) → p5)) ∨ p4))) ∨ ((p4 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116028875118425520868024941190 : (((p4 ∧ ((p2 → True) → p4)) → (((p5 → (p5 → (((p5 → (p3 ∧ False)) ∨ p4) ∧ True))) ∧ p2) ∨ ((p3 ∨ False) ∧ True))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254409156317645971651505985454 : ((p2 ∧ p5) → (((((((p1 ∨ True) ∧ False) ∧ p3) ∧ (p1 ∧ True)) ∨ ((True ∧ p2) ∧ p2)) ∧ (False ∨ True)) ∨ ((p5 ∧ (p2 ∨ p1)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198202616116207896946163598972 : (((p3 → False) → (p2 → ((False ∨ False) ∧ p1))) ∨ (((p2 ∨ (p3 → p2)) ∧ ((p3 → p4) → False)) ∨ ((False → ((True ∨ False) → p4)) ∨ False))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184455741202010735295664846448 : (((p4 ∨ ((p1 ∨ (p5 ∨ p3)) → (False ∨ p1))) ∧ (True → False)) ∨ (True ∧ (p3 → ((((p5 ∨ p4) ∨ False) → p3) ∧ ((p4 ∨ True) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47525888174628844454456277093 : (((p3 ∨ (p4 ∨ (((((p5 ∨ (p3 → p1)) ∨ (False ∧ p4)) ∧ ((p2 ∨ p3) ∨ (True ∧ True))) ∧ (p1 → p1)) → p5))) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638262642492637990439138315334 : (((((p3 → ((p5 → ((True ∧ p3) → False)) ∨ p2)) → ((((p5 ∨ p5) → p1) → (True ∧ ((False ∨ (p4 ∧ p5)) ∧ False))) → p4)) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601679567757656553903190558595 : ((((p3 ∧ (p5 ∨ ((p1 ∨ (p2 ∨ p5)) ∨ ((False ∧ (p3 → (((((p5 → p3) ∧ p4) → (p3 ∨ p4)) ∧ p2) ∧ p5))) ∨ True)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53333400257544333844126127170 : (((((p5 → ((((p4 ∨ False) ∨ p1) → False) ∨ True)) ∨ p3) ∧ True) → ((p2 ∧ (((p1 → p4) ∨ p3) ∧ (p2 → (p3 ∧ p4)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118872500317927396104190226969 : ((True → ((p1 ∧ True) ∧ ((p1 → False) ∨ (p3 ∨ (False ∨ ((True ∧ ((p3 → (p2 ∨ ((False ∨ p3) → p2))) ∧ p5)) → False)))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142655683220319061818812336921 : ((p1 ∨ ((p3 ∧ (True ∨ (True ∨ (((p3 → (((p3 → p4) ∨ (p3 ∨ False)) ∨ p1)) → False) ∨ p4)))) ∧ (p5 → True))) → (p4 ∨ (p2 ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
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
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249110436378763133025131205751 : ((p4 ∨ p2) ∨ ((p1 ∧ ((False → (((False → ((((p1 ∨ p5) ∨ True) ∧ p2) ∨ (p1 ∧ p2))) → p1) ∨ p2)) → ((True → p1) ∨ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777618126648128131179799777127 : (((p1 ∨ (((p1 ∨ ((p4 ∨ p5) ∨ (p1 → (p3 ∨ True)))) ∨ p3) ∨ ((((p4 ∨ ((p2 ∧ p5) ∨ (p5 ∨ False))) ∧ p2) → True) ∧ False))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117208609809485502699865482827 : ((True ∧ ((True → ((p1 → p4) ∧ (p5 → p2))) ∨ (True → (((p3 ∧ (p5 ∧ (p3 ∧ p1))) ∨ p2) ∨ ((False ∧ True) ∨ p4))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190592122347054440358495800448 : ((((p2 → p4) ∧ (((p5 ∨ p2) ∧ p3) → p5)) → p1) ∨ (((p3 ∧ True) ∨ (p1 ∨ (p3 ∧ p1))) → (((p5 ∧ p1) → (True ∧ p1)) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_78955052459070967676251829549 : (((p1 ∧ ((p3 ∧ (((False ∧ (False ∨ p4)) ∨ (((p4 ∨ p3) → (p1 → True)) ∨ (p5 ∧ p5))) → False)) ∧ (p4 → p4))) ∧ (True → p4)) → p5) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : ((False ∧ (False ∨ p4)) ∨ (((p4 ∨ p3) → (p1 → True)) ∨ (p5 ∧ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h13 := h9 h10
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164556187231187987681102899773 : ((((((False ∨ (p1 ∧ p2)) → p1) ∨ p2) → ((p2 → True) → ((p1 ∨ p4) ∨ False))) ∧ p4) ∨ (False → (p4 ∧ (p1 ∧ (False → (True → p5)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245774167281522234263477823543 : ((p3 ∧ p3) ∨ (((((p3 → (False ∧ (((False ∧ p3) → p4) → p2))) ∨ (p2 → p5)) → p1) ∧ ((((p5 ∨ p1) ∨ True) ∨ p2) ∧ p5)) → p1)) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : ((p3 → (False ∧ (((False ∧ p3) → p4) → p2))) ∨ (p2 → p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h9
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h14 : ((p3 → (False ∧ (((False ∧ p3) → p4) → p2))) ∨ (p2 → p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h14
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : ((p3 → (False ∧ (((False ∧ p3) → p4) → p2))) ∨ (p2 → p5)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h18
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166394041324107214617289409616 : ((False ∨ ((True → p3) ∧ ((p3 → True) → ((p1 ∨ (p3 → ((True ∨ p4) → p1))) → p1)))) ∨ ((((p1 ∨ p3) → (p2 ∨ p2)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194003015273653642904738391851 : ((p4 ∨ ((((p3 → True) ∨ True) ∧ (p2 ∨ True)) ∨ False)) → (((p2 ∧ p4) ∧ (p5 ∧ (False ∧ (p1 ∨ ((False ∧ True) ∧ (p5 ∨ True)))))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
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
        cases h6
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
theorem thm_5_vars_351468913707656056753403002647 : (p4 → ((True ∨ (((p1 ∧ p5) ∧ ((True ∧ p5) → (p1 ∧ ((((False ∨ p4) ∨ p2) → True) ∨ p2)))) → p2)) → ((p1 ∧ (p3 ∧ p1)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49365755604664188702341201887 : (((p3 → (True → (((p1 ∧ (p4 → (True → p3))) → ((p1 → p5) ∧ False)) ∧ (((True → p5) → p2) → p4)))) ∨ ((p5 → p2) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40467870384988497164815647685 : (((((p2 ∧ (p1 ∧ p5)) ∨ (((((((((False ∨ p5) → p3) ∧ False) → p5) → p1) ∨ (p2 ∨ p4)) ∧ p1) ∨ p2) ∧ p1)) ∨ p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53208581759981411378959896363 : ((((((p2 ∨ p5) ∨ (p4 ∨ p2)) → p2) ∧ (p1 → (p3 ∨ p2))) ∨ ((p2 → False) → (((p3 → ((p2 ∧ False) ∨ p3)) ∧ p4) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115671440563436774688619612262 : ((((p1 ∨ p2) → (True → (False ∨ p1))) ∨ (p5 ∧ ((p3 ∧ p5) → ((False ∨ (False ∨ (p4 ∧ (p1 → (p2 → False))))) ∧ p1)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323499529673899171312234846905 : (p5 ∨ (((((p2 ∨ p5) → ((p1 ∧ True) ∧ (p1 → p2))) ∨ p4) → (p1 ∨ (p1 → (False ∧ (False ∨ (p3 → p2)))))) ∨ ((p5 → True) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613734708149023514382797606271 : ((((((False ∨ p5) → ((p1 ∧ (p3 ∨ (((p4 ∧ (p3 ∧ (False ∨ False))) ∨ p5) → (p2 ∨ p1)))) ∧ p4)) ∧ ((True → p4) → p2)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_49247727508864169876179979089 : ((((p5 → p3) → ((p5 ∧ (((True → p5) ∧ (((p3 ∨ p4) ∨ (p1 → p5)) ∨ p3)) ∧ p2)) ∨ (p3 ∨ True))) ∨ ((False ∧ p1) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2196794596765493105010540562 : (((p4 ∨ p4) → (((True → (p3 ∨ p5)) → ((p1 → False) ∧ (p1 ∧ False))) ∨ p4)) ∨ (((False ∨ p1) ∧ ((True ∧ p4) ∨ p5)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165012667321544744342398758658 : ((((p3 ∨ ((p2 ∨ (False → p2)) → p5)) → ((p5 → (True → (p5 ∨ p3))) → p5)) → p3) ∨ ((((True ∨ p5) ∧ (False ∧ p4)) ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227440499757074814573324808503 : (((p5 → p4) → False) ∨ (((p5 ∧ p3) ∧ True) ∨ ((((p2 → (p1 ∧ p1)) ∨ ((p3 ∨ (True ∨ p5)) → True)) → ((False → p4) ∧ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69987378414672564341261306897 : (((((((p1 ∧ (((p3 → ((p4 ∧ p5) ∨ True)) → p3) ∨ (p2 ∧ (False ∧ p4)))) ∧ ((p2 ∧ False) → True)) ∨ p5) ∨ True) → p5) ∧ True) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p1 ∧ (((p3 → ((p4 ∧ p5) ∨ True)) → p3) ∨ (p2 ∧ (False ∧ p4)))) ∧ ((p2 ∧ False) → True)) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748197229186466898057115024016 : ((((p1 → p5) → ((p5 → ((((p2 → (p5 → ((p2 ∧ False) ∨ p1))) ∨ True) → p3) ∨ (p2 → (p1 → p1)))) ∨ (p1 ∧ (p1 ∨ p5)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135451786522701921773310078719 : (((((((False ∧ p1) ∨ p3) ∧ p4) → ((False ∨ ((p4 → p5) → p1)) ∧ (p3 → p2))) ∨ False) → (False ∧ (False ∧ p1))) ∨ ((p5 → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181221415531697188191527006074 : ((p2 ∧ (p2 → (p5 ∧ (True → (((p3 → p5) ∧ p3) ∧ (p5 → p3)))))) → ((False ∨ ((p3 ∨ (p2 → p3)) ∨ (False ∧ (p1 ∨ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173339304666183399996552634033 : ((p2 → (False ∨ (p4 ∧ ((True ∨ (((p4 ∧ (True ∨ p2)) ∧ True) → p4)) → p5)))) ∨ ((p5 → ((p2 → ((False → p5) ∨ p2)) ∧ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180283428617716986253094388510 : (((p4 → (False → ((p3 ∧ p5) ∨ (((p1 ∧ p4) → p5) ∨ p1)))) → p1) → (p5 → (((p2 ∧ ((False ∨ p1) → (p2 ∨ False))) ∨ True) ∧ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



