variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147562655575591457633369610332 : (((((((True ∧ p3) ∧ p5) ∧ (p4 ∨ ((p2 → (p4 ∨ (p3 ∧ (p1 → p1)))) → p1))) → p4) ∧ p1) → p5) ∨ (p5 → (True ∨ (p2 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_863772537893368072971780155755 : ((((((p3 → ((p2 ∨ p2) ∧ (p4 → (p4 ∨ (p2 → True))))) ∨ p4) → ((p5 → p1) → (p1 → ((True → p3) ∨ (p1 ∨ False))))) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → ((p2 ∨ p2) ∧ (p4 → (p4 ∨ (p2 → True))))) ∨ p4) → ((p5 → p1) → (p1 → ((True → p3) ∨ (p1 ∨ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42302505654204271693751752295 : (((p2 ∧ (((p3 ∧ (p1 → (((p3 → p1) → (True ∨ p3)) ∨ p4))) ∨ (p2 ∧ (p3 → ((False → p4) ∨ True)))) → (p5 → p4))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178671692527094553259795677663 : (((p3 ∧ (p5 → (p5 ∨ p4))) ∧ (p3 ∨ ((False ∧ (p1 → False)) ∨ p2))) ∨ ((((True ∧ p3) ∨ (((p3 ∨ p4) ∨ p2) ∨ True)) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616398977014832325142219706917 : (((((((((False ∧ True) ∧ (p2 ∨ p1)) ∧ (p1 → True)) ∧ False) ∨ True) → (p4 ∨ ((True → (((p1 → False) ∧ p3) ∨ p3)) ∨ p4))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_683589833581847926462648289181 : (((((((((p4 ∧ True) → (True → ((p1 ∨ False) ∨ p2))) ∨ (p5 → p5)) ∧ p2) → p3) ∧ p2) ∨ (((p3 ∧ False) ∨ p1) ∧ (p1 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254342602836894520953759460744 : ((p2 ∧ p4) → (((((p2 → p4) ∨ False) ∨ (p4 ∧ (p3 ∨ False))) → ((p4 ∧ p5) ∨ ((p4 ∨ ((p4 ∨ False) → p5)) → p1))) ∨ (False → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741161817981337772896667211869 : ((((p4 ∨ p1) ∨ ((p1 ∨ True) ∧ (((p5 ∧ ((False ∨ p5) ∨ p1)) ∧ p5) → (p3 → ((p5 ∧ False) ∨ ((p3 ∨ (True ∨ p3)) ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55063165237321618909080232005 : (((p3 ∨ ((p3 → (p2 → p1)) ∧ p3)) ∧ (((p5 → (True ∧ ((p3 ∨ ((p4 ∧ p2) ∧ p4)) ∨ p4))) → (p3 ∧ p2)) → (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186064243715492719520733082900 : ((((p3 ∧ (((p4 → (False → p5)) ∨ True) ∨ False)) ∨ False) ∨ p3) → (((p3 ∨ True) → ((p2 → ((p3 → (p1 ∧ False)) ∨ True)) ∨ False)) ∨ p4)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h8
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h10
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h11 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h12
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h14
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h18
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h24
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h25 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h26
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247965716420901006871048003417 : ((p1 ∨ p4) ∨ (((((True ∨ (p3 ∨ p1)) → False) ∧ ((p2 ∨ ((p5 → True) → p1)) ∨ ((False → True) ∧ True))) → (p5 ∧ p2)) ∨ (p2 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True ∨ (p3 ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : (True ∨ (p3 ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : (True ∨ (p3 ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- Conjunctions on the left can always be decomposed.
  let h16 := h1.left
  let h17 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h21 : (True ∨ (p3 ∨ p1)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h22 := h16 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h26 : (True ∨ (p3 ∨ p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h27 := h16 h26
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187079888341400801689250642988 : (((True → p4) ∧ (((False → p1) → p3) → ((p5 → False) → True))) → ((((p4 ∧ ((p5 ∨ (p5 → p3)) ∨ p4)) ∧ p3) ∨ p4) ∨ (True → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66190426755877217775554958861 : ((p5 ∨ (((((True → p5) ∨ ((p1 ∧ (p4 ∨ p3)) ∧ False)) ∧ (True → (p4 → p3))) → p2) ∧ (p2 → (((False ∨ p3) ∨ p2) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112122287050919806007910139918 : (((True ∧ (((p5 ∧ (p2 ∧ (((p1 ∧ False) ∨ (p1 ∧ False)) ∨ True))) ∨ (False ∧ True)) ∨ (((p1 ∧ p2) ∧ p4) ∧ p4))) ∨ True) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185497861138846192250016380547 : ((p2 ∨ (((p4 ∨ p2) ∨ (True ∧ (p1 ∨ False))) → (False ∨ p4))) ∨ ((True ∨ ((p4 ∨ p1) ∨ (((p3 → p1) → p1) → (True ∨ p4)))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165029386339211095296917059478 : ((((p1 ∧ (False ∨ p4)) ∨ ((((p5 ∨ (p2 → (p1 ∧ p2))) ∧ True) ∨ p1) ∨ True)) → p5) ∨ (False → (p3 → ((p1 ∧ (False ∨ p1)) ∧ p5)))) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136946399757300339447816574304 : (((p5 → p1) ∨ (p5 ∨ ((True → ((False ∧ ((p1 ∨ p2) → (p2 → True))) ∨ (p2 ∧ (p2 ∧ False)))) ∨ (p4 → True)))) ∨ ((p3 → True) ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_300247699388427021081687849763 : (False ∨ (((p1 ∨ p2) ∨ ((((True → p4) ∨ (p2 → ((p4 ∨ ((p2 ∨ False) ∨ p5)) ∨ p1))) ∧ p1) ∧ ((p1 → p5) ∨ p3))) → (p2 ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232906744538662451889648732688 : ((p3 ∧ (p3 ∧ p1)) → (((False → p2) → (p2 ∧ (p2 ∧ (((True → (p5 → p3)) ∧ ((p1 ∨ p1) → (p4 ∨ p5))) ∧ False)))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354912510247766342374800628589 : (p5 → ((False ∨ ((p2 ∧ ((((p3 ∨ False) ∧ p3) → (p2 → p4)) → p2)) ∨ ((p1 ∨ p5) ∨ (False ∧ (False → ((False → False) ∧ p5)))))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112083300485476405031319832039 : ((((False ∨ p5) ∨ (p3 ∧ (((((True ∧ ((((True ∧ p5) ∧ False) ∨ p4) → p5)) ∧ p1) ∧ p4) → True) ∧ (p4 → False)))) ∨ p4) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608598967248741049370913928385 : (((((((((p5 ∨ False) → (p4 ∨ (((p1 → (p4 ∨ p4)) → p4) → p3))) ∧ (p1 → p3)) ∧ (p4 ∧ p3)) ∧ (p4 ∨ p4)) ∨ True) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_65221745378584053102330169389 : ((p3 ∨ (((p4 → p5) ∧ ((((p4 ∧ p3) ∧ ((p5 ∧ p1) ∧ ((((False ∧ p2) → p1) → (p1 ∧ True)) ∧ p2))) → True) → p1)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348847847399561891903845871095 : (p3 → (p2 ∨ ((((((p4 ∨ ((((True ∨ p4) ∧ (p2 → p2)) ∧ p1) ∨ (p5 → p1))) ∧ p2) ∨ p2) ∨ (p4 → (p3 ∧ p1))) ∨ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193030916838414765506756649426 : (((True ∧ (p2 → ((p3 ∧ p4) → p2))) → (False ∨ p4)) → ((p5 ∨ ((((p3 → p3) → False) → p4) ∧ p4)) ∨ ((False ∧ p1) ∧ (p4 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (p2 → ((p3 ∧ p4) → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_549834437166361720385764916990 : (((p1 ∨ ((p1 → (((((True ∧ (((False ∨ p4) ∧ p4) → (p4 → p4))) → (True ∧ p2)) ∧ p4) ∧ p4) ∨ (p1 ∨ (p5 ∧ p3)))) ∧ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324491649372985479630272756322 : (p5 ∨ (((True ∧ p2) ∧ (p4 ∨ p1)) ∨ (p1 ∨ (((p5 ∨ False) ∧ (p3 ∨ ((False ∨ ((p4 ∧ (p3 → False)) → False)) ∨ (p2 ∨ False)))) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160460422442352343602196518291 : (((((p4 ∨ p5) → (p3 ∧ (p4 → False))) ∧ (p1 ∨ ((p3 → True) ∨ p1))) → (p4 ∧ (p4 ∨ p5))) → (p3 ∨ ((False ∨ True) ∨ (True → True)))) := by
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
theorem thm_5_vars_165040438789057052821416973342 : ((((p1 → True) ∧ ((p3 ∧ p2) ∨ ((p5 → True) ∧ ((p1 ∧ True) ∧ (p1 ∧ True))))) → p4) ∨ ((((p3 ∨ True) ∧ (p5 ∨ True)) ∧ p3) → p3)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118504613950012291422992881118 : ((p3 ∨ ((((p5 ∧ ((p5 ∨ p4) ∨ False)) ∨ p4) ∧ p5) → ((((p1 ∨ (p3 ∨ (False ∧ p5))) ∨ False) ∧ (p2 ∨ p1)) ∨ True))) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
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
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161498852623476376241456436344 : ((p4 ∧ (((((False → ((((True ∧ p3) → p3) ∧ p2) → p4)) ∨ True) ∨ True) → False) ∧ (False → p2))) → ((p2 ∨ p1) ∧ (p3 ∨ (p1 ∧ p4)))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (((False → ((((True ∧ p3) → p3) ∧ p2) → p4)) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h12 : (((False → ((((True ∧ p3) → p3) ∧ p2) → p4)) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61840327938353933875780722751 : ((p2 ∧ ((((p2 → p1) → ((p3 ∨ ((False ∧ True) ∨ (((p2 → p3) ∨ p3) ∧ p5))) ∨ (p4 ∨ ((p5 ∧ False) ∨ p5)))) ∨ p1) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614531315360200089300444969029 : (((((((((p1 → True) ∨ p1) → p5) ∧ (False ∨ (p5 → True))) ∧ ((p4 ∧ p5) → (p3 ∨ p2))) ∧ (True → (True ∨ (p5 → p4)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259552957811796484026072215831 : ((p1 → True) → (((((p4 ∨ ((p3 ∧ p2) → p4)) → (p2 → ((p4 ∨ (True ∨ (p1 ∨ False))) ∧ False))) ∧ ((p5 ∨ p5) → p5)) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148333910988089214518314179363 : (((((True → (False ∧ ((False → p3) ∧ (p3 ∧ True)))) ∧ (p4 → p4)) → p4) ∧ (False ∨ ((p2 ∧ p4) ∨ True))) ∨ (((p2 → p5) ∧ p1) → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166277043430183192055124781683 : ((p4 ∧ ((((True ∧ (p4 ∨ ((p5 → p1) ∨ p3))) → (p3 → p4)) ∨ (p5 ∧ p2)) ∧ p5)) ∨ (p4 → ((p4 ∧ p1) → ((p5 → p3) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348206590364655723812338674127 : (p3 → ((p1 → True) → (((p3 ∧ True) ∧ p2) → ((((p4 ∨ p3) ∨ (True ∨ p3)) ∨ p3) → (p1 ∨ ((p5 ∧ p1) ∨ ((p5 ∧ False) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h3.left
        let h9 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h3.left
        let h17 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h18 := h16.left
        let h19 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h3.left
        let h26 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h27 := h25.left
        let h28 := h25.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h3.left
        let h34 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h35 := h33.left
        let h36 := h33.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h37
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- False on the left can always be used.
        apply False.elim h39
  case inr h40 =>
    -- Conjunctions on the left can always be decomposed.
    let h41 := h3.left
    let h42 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h43 := h41.left
    let h44 := h41.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h45
    -- Conjunctions on the left can always be decomposed.
    let h46 := h45.left
    let h47 := h45.right
    -- False on the left can always be used.
    apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185908305770433725041901706880 : ((((p2 ∧ (p3 → (p5 ∧ False))) ∧ (p3 → (p5 ∧ p5))) ∧ p3) → (((p3 ∨ p4) → p1) ∧ (True → ((p3 → (p4 ∨ p4)) ∧ (p3 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- False on the left can always be used.
    apply False.elim h22
  -- Implications on the right can always be decomposed.
  intro h23
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h1.left
  let h26 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h27.left
  let h30 := h27.right
  -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
  have h31 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h26
  -- We have shown the premise of h30, we can now drive its conclusion.
  let h32 := h30 h31
  -- We need to get the right conjuct of h32 based on <expert-advice>.
  let h33 := h32.right
  -- False on the left can always be used.
  apply False.elim h33
  -- Conjunctions on the left can always be decomposed.
  let h34 := h1.left
  let h35 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h36 := h34.left
  let h37 := h34.right
  -- Conjunctions on the left can always be decomposed.
  let h38 := h36.left
  let h39 := h36.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590793871796551142989869232619 : (((((p2 ∨ ((((p4 ∨ (p2 ∨ ((p3 → ((True ∨ p3) → (p5 ∧ p1))) ∨ False))) ∨ (False ∨ True)) ∨ (p4 → p5)) → p3)) → p4) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178127359092667078804001790696 : ((((((p1 ∨ (p4 ∧ p1)) → p1) → p3) → (p1 ∨ (p3 → True))) → False) ∨ (True ∧ (p2 → ((False ∧ p4) → (((p4 ∧ p5) → p3) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h8 := h2.left
  let h9 := h2.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165425410434877713233604414700 : ((((True ∧ (p5 → p5)) ∨ (p4 → ((p5 → (False → p1)) ∨ p4))) → (False ∨ (p3 ∧ p2))) ∨ ((True ∧ ((p4 ∨ p2) → (p1 → p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260318806327110689526918331229 : ((p2 → p4) → (True ∧ (((True → (p1 ∧ ((True → p1) ∧ ((p5 ∧ p5) ∧ (p1 ∨ (((p2 ∨ False) ∨ True) → p1)))))) ∨ (p3 → p3)) ∨ True))) := by
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
theorem thm_5_vars_347096974752165466258972933089 : (p3 → (((p2 → (False ∨ ((p4 ∨ True) → ((p5 → (p1 → True)) → p1)))) ∧ p4) ∨ ((p3 ∧ (((p4 ∨ p1) → p3) ∨ True)) ∨ (p1 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758569063451030424318791588831 : (((p2 ∧ ((((p1 ∧ p2) ∨ ((((True → True) → ((p1 ∨ ((p1 ∧ p1) → False)) → p2)) ∧ (True ∧ True)) ∨ (p3 → p2))) ∨ p4) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349937273588027813653405857410 : (p4 → ((((True ∧ ((p2 ∨ ((((p5 ∨ p5) ∧ (p3 → (True ∨ p1))) → p4) → ((p1 ∨ p5) ∧ (p2 ∧ p2)))) ∧ True)) ∧ p2) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258253763363271956111470627398 : ((p4 ∨ p5) → ((p4 → False) → (((p5 ∨ ((p4 ∨ p5) ∨ (p3 ∨ p2))) → True) → (((False ∧ p5) ∨ (p5 ∧ p3)) ∨ (p5 ∧ (p5 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779231956066199317071706689086 : (((p2 ∨ ((((False → ((p1 ∨ p3) ∧ True)) → p4) ∨ ((p1 → ((True → (p4 ∧ (p4 → (p3 ∧ (p1 ∨ p4))))) ∧ p2)) ∨ p5)) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47401938998042904714910392000 : (((True ∧ ((p2 → (p5 → True)) → ((False ∧ ((p5 → ((p3 ∨ p2) ∧ p2)) ∧ True)) ∨ (p5 ∨ (p4 → (p4 → p1)))))) ∨ (True ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64705064027337865489978090695 : ((p1 ∨ (p1 → (((((p1 → False) → (p4 ∧ (((p2 → p3) ∨ ((p2 ∧ p2) ∧ p3)) ∨ p3))) ∧ False) ∨ p3) ∨ (p2 ∧ (False ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234158363571594288232837809487 : ((True → (p1 → p5)) → ((((True → (p3 ∨ (((p5 ∨ (True ∧ p3)) → p4) ∨ (False ∨ p1)))) ∧ p5) ∨ True) ∨ (((p1 ∨ p5) ∨ p1) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219367115752556552014205700550 : ((p3 ∨ ((p4 ∨ True) ∨ True)) → (p2 → ((p2 ∧ p4) ∨ ((p4 ∧ ((p3 ∨ (p2 ∨ ((p3 → False) ∨ p5))) ∨ False)) → (p1 ∨ (p4 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
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
        exact h5
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h5
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h2
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
          case inr h24 =>
            -- Disjunctions on the left can always be decomposed.
            cases h24
            case inl h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h26 =>
              -- Disjunctions on the left can always be decomposed.
              cases h26
              case inl h27 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h20
              case inr h28 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h20
        case inr h29 =>
          -- False on the left can always be used.
          apply False.elim h29
    case inr h30 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h34
        case inl h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h36 =>
          -- Disjunctions on the left can always be decomposed.
          cases h36
          case inl h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h32
          case inr h38 =>
            -- Disjunctions on the left can always be decomposed.
            cases h38
            case inl h39 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h32
            case inr h40 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h32
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54112348226152613274290395997 : (((p3 ∧ (p1 ∨ (True ∨ (p3 → ((p5 → p1) ∧ p1))))) → (((p5 → p2) → (((p2 ∨ (p3 ∧ (False ∨ p3))) ∧ p4) ∨ p3)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148280645041080908954846697316 : ((((True → ((False ∨ p4) → ((p4 ∨ (False → False)) ∨ (p2 ∨ (True → p3))))) ∨ p2) → (p5 → (p3 ∨ p2))) ∨ ((p2 ∧ p2) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233260857566901279850252548008 : ((True ∨ (p3 ∧ p1)) → (((((True → False) ∨ False) ∨ p1) ∨ (False → (((True ∧ p2) ∨ True) ∧ (((p5 → (p5 ∧ False)) → p5) ∧ p2)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244686370299286300967036093499 : ((p1 ∧ True) ∨ (((((p2 → (p2 ∧ True)) ∧ True) ∧ ((p4 ∨ (((p4 ∨ p2) ∧ p5) ∧ p4)) ∧ p3)) ∨ ((p1 → True) ∨ p3)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348763133055091236363807442443 : (p3 → (False ∨ ((p2 ∨ p4) → ((p1 ∨ ((p1 ∧ ((p1 ∧ (p2 ∧ p4)) → p1)) ∨ ((False → p3) ∨ (p2 ∨ (p5 ∧ False))))) ∨ (p2 → p2))))) := by
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
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37756150933497391199605675882 : ((((((p4 ∧ (p5 ∧ p5)) → p2) ∨ (((p2 ∨ (p3 → (p1 → False))) ∨ (False → p2)) ∧ (((p3 ∧ False) ∨ p4) → True))) → p2) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338402755592832070603678842922 : (p1 → ((((p2 ∨ p1) ∨ p1) → p2) → ((p5 → ((True ∨ ((((True ∧ (p4 ∨ True)) ∨ (p3 ∨ (p5 ∧ p1))) → True) ∧ True)) → p2)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 ∨ p1) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
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
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148832563123881888922960711125 : ((((p2 ∧ (True ∨ p3)) ∧ p4) ∧ (((((p5 → p2) → p2) ∨ p2) → ((p4 → (p2 ∨ p1)) → p5)) ∨ p1)) ∨ ((p5 ∧ (True ∧ p3)) → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43552354180568244735954045228 : (((((((p2 ∧ (p3 ∨ p1)) ∧ (((p2 → (p4 → ((p1 ∧ (False ∧ p4)) → p3))) ∧ (False ∨ p5)) ∧ p3)) ∨ True) ∧ True) → p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38166679457827401504348057866 : (((((p1 ∧ (p1 ∧ (p3 ∧ (p4 ∧ (((p5 ∧ p1) ∧ p5) → False))))) ∨ (p1 ∧ (p2 ∧ (p2 ∧ p3)))) ∨ ((p1 ∧ p5) ∨ True)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264848341092994255004897954094 : (True ∧ ((p3 ∨ p3) ∨ ((((((p4 ∨ True) ∨ (p3 ∨ (p5 → p5))) → ((p3 ∨ (p2 ∨ p4)) ∨ p5)) → (p1 ∧ (True ∨ p2))) → p3) ∨ True))) := by
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
theorem thm_5_vars_763878224811792371396599482068 : (((p3 ∧ (p4 ∨ (p2 ∧ (False ∧ (p2 ∧ (p3 ∨ (True ∧ (((((p2 ∨ p5) ∧ False) ∧ (True ∧ p4)) ∨ (p1 → (p3 ∨ True))) → p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183466461482914623041294361568 : ((p2 ∨ (p2 → (p5 → (True ∨ (False → (p1 → (p2 → False))))))) ∧ (((p4 ∨ (p2 ∨ (True → p4))) ∨ True) → (p5 ∨ (True ∨ (False ∨ p3))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719941386485520026939046732335 : ((((p5 → (False ∨ (p2 ∧ p1))) ∨ ((p1 → (p4 → ((p4 ∧ (p4 ∨ p1)) ∧ (((p3 ∧ p3) ∧ True) ∨ ((True ∨ p4) ∨ True))))) ∨ p5)) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157830271901433429280968341076 : (((p5 ∧ (((p4 ∧ p5) ∧ ((True ∧ p2) → (p5 ∨ p1))) → p3)) → (p1 ∨ (False ∧ (p5 ∨ p3)))) ∨ ((p2 → (p4 ∧ (True → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40490421236723392798565135725 : (((((p5 ∧ True) → ((False ∨ (p3 ∨ ((((p4 ∧ (p2 → (p2 ∨ p5))) ∧ p2) ∧ p3) ∧ p1))) ∨ ((True → True) ∨ p2))) ∨ p2) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157862446854761636955115359195 : (((p4 ∨ (((((p4 ∧ p2) ∨ p2) ∧ p3) ∨ p1) → p1)) ∧ (((p5 → True) → p4) ∨ (p4 → False))) ∨ (p2 → (p5 ∨ (p2 ∧ (False → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622882710553248139545747133154 : ((((p5 ∧ ((True ∧ (False → (p5 → (((((p5 → p4) ∨ p1) ∨ (((p2 ∨ p3) ∨ p4) ∨ (False ∧ p2))) ∧ True) ∧ p2)))) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46606947866988704079003332171 : (((p2 ∧ ((((p1 → (p3 ∧ p5)) ∧ p5) ∨ (p4 → p5)) ∧ (((p3 ∨ ((p2 ∧ p3) ∧ p1)) ∨ (True ∨ p1)) ∨ p5))) ∧ (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609202335524840124368347542440 : (((((((p5 → p1) ∨ p1) ∧ ((p2 ∧ ((p4 ∧ ((True ∨ p1) → (p1 ∨ (p2 ∨ False)))) ∨ (p5 ∧ p5))) ∨ (p2 ∨ False))) ∨ True) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_61352770073083098850455290831 : ((p1 ∧ (((p3 → ((p2 ∧ p4) → p5)) ∧ ((p3 ∨ ((((False ∨ (p3 → (p5 ∨ p1))) ∧ True) ∨ False) ∧ True)) ∨ (True ∧ p5))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328555220463586898746315638188 : (True → (((((p5 ∨ p5) ∨ p1) ∨ (p2 ∨ p4)) ∧ ((True ∧ p3) ∨ ((p2 → p2) ∨ p3))) → (p3 ∨ ((False ∧ (p4 ∨ False)) → (p1 → p5))))) := by
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
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- Implications on the right can always be decomposed.
            intro h14
            -- Conjunctions on the left can always be decomposed.
            let h15 := h13.left
            let h16 := h13.right
            -- False on the left can always be used.
            apply False.elim h15
          case inr h17 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h24
            -- Implications on the right can always be decomposed.
            intro h25
            -- Conjunctions on the left can always be decomposed.
            let h26 := h24.left
            let h27 := h24.right
            -- False on the left can always be used.
            apply False.elim h26
          case inr h28 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h35
          -- Implications on the right can always be decomposed.
          intro h36
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- False on the left can always be used.
          apply False.elim h37
        case inr h39 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h40
    case inl h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h42 =>
        -- Conjunctions on the left can always be decomposed.
        let h43 := h42.left
        let h44 := h42.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h44
      case inr h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h47
          -- Implications on the right can always be decomposed.
          intro h48
          -- Conjunctions on the left can always be decomposed.
          let h49 := h47.left
          let h50 := h47.right
          -- False on the left can always be used.
          apply False.elim h49
        case inr h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h51
    case inr h52 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h53 =>
        -- Conjunctions on the left can always be decomposed.
        let h54 := h53.left
        let h55 := h53.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h55
      case inr h56 =>
        -- Disjunctions on the left can always be decomposed.
        cases h56
        case inl h57 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h58
          -- Implications on the right can always be decomposed.
          intro h59
          -- Conjunctions on the left can always be decomposed.
          let h60 := h58.left
          let h61 := h58.right
          -- False on the left can always be used.
          apply False.elim h60
        case inr h62 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h62



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167606771645706665406736597915 : (((p2 → ((((False ∧ True) ∨ ((False → (p1 → p5)) ∧ p5)) ∨ False) ∧ True)) ∨ (p2 ∧ p2)) → (p2 → (((p1 ∨ (p4 ∧ p1)) ∨ p1) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245358993268573189877485697212 : ((p2 ∧ p3) ∨ (((p1 → (((((((p3 ∧ p4) ∧ (p3 ∧ False)) → p4) ∧ p3) ∨ p3) ∨ p3) ∧ False)) ∧ (True → p1)) → ((p1 ∨ p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613634591227293681638383222390 : ((((((((p2 → (((p4 ∨ p3) ∨ p1) → ((False ∨ p2) ∧ p3))) ∨ False) ∨ True) ∧ ((p4 → False) ∨ p5)) ∧ ((p4 ∨ p3) ∧ p3)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_808772399615479982812312718479 : (((p4 → (p4 → ((((False ∧ (p4 ∨ False)) ∧ p5) ∧ (((p5 → p4) → ((p1 → p2) ∧ (p1 ∨ p5))) ∧ (p4 → p4))) ∨ (p3 → p3)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9925711281948484948617936440 : (((p1 ∧ (p2 → (((p5 ∨ (((((p5 ∨ p4) ∧ p3) ∨ p2) ∨ p3) ∨ p3)) ∨ (p5 → False)) ∨ (False ∧ ((p5 ∧ p3) ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150088372023538017744953970426 : ((True → (True → (p5 ∨ (p4 ∧ ((((p2 ∧ (((p1 ∨ False) ∧ p2) ∨ True)) ∧ True) → (p2 → p1)) ∧ p5))))) ∨ ((p4 → (False ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313609926122718016740874497834 : (p3 ∨ (((p3 → (False ∧ ((p1 ∧ p4) ∧ p5))) ∧ (((p1 → p4) → p3) ∧ ((p3 ∧ (True ∨ p3)) ∧ ((p1 → (p3 ∨ p3)) ∨ p4)))) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- We need to get the left conjuct of h22 based on <expert-advice>.
      let h23 := h22.left
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h25
      -- We need to get the left conjuct of h26 based on <expert-advice>.
      let h27 := h26.left
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90874031359509310071196234234 : (((p5 ∨ True) ∧ (((((p2 → p1) ∧ p4) → (p2 ∧ False)) ∧ (p1 ∧ ((((False ∨ (False ∨ p2)) ∧ p2) ∧ p5) → (p5 → p2)))) ∨ p1)) → p1) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218827934451626796139185064622 : ((p2 ∧ ((p5 ∨ p3) ∧ p3)) → (((p4 ∨ p4) → (p5 ∨ (p2 ∨ p5))) ∧ ((p5 ∧ p3) ∨ (p5 ∨ ((((p1 ∨ p3) ∧ p5) ∧ p1) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h18.left
  let h20 := h18.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612395006053428615383531250043 : (((((True → ((p4 ∧ (p3 ∨ p2)) ∨ ((((p5 ∧ p2) ∧ ((True ∧ (p4 → p4)) → True)) ∧ (True ∨ p2)) ∧ p3))) ∧ (True → p1)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_257690224675517513019213036093 : ((p3 ∨ p3) → (((((False ∨ (p1 → ((p3 → p5) → p1))) ∧ False) ∧ ((p1 ∧ p3) ∧ p1)) ∨ p5) ∨ (p1 ∨ (False ∨ (True ∨ (p2 ∨ p3)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_150472255437882789108319140664 : (((((p3 ∨ True) → (p3 → (p4 ∧ ((((p1 → p3) ∨ (False ∨ p3)) ∧ p3) → p3)))) ∧ (p5 → p3)) ∧ p5) → (((p5 → False) ∧ p3) ∨ p4)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p3 ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257761629553578007150138537393 : ((p3 ∨ p4) → (((p2 ∨ p1) ∧ p3) ∨ ((True → (p1 ∧ ((False ∧ ((p4 ∨ (True ∧ (p1 → (False ∨ p4)))) → False)) → (p3 → False)))) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625106488444651558704138967229 : ((((True → ((False ∧ (((p2 → (p4 ∨ (False → (p4 → (False ∨ (p3 → ((p5 ∨ p5) ∧ p1))))))) → p5) ∨ p4)) ∨ (True → False))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_658574774213244006171471368006 : ((((p2 ∨ (p4 → ((p2 ∨ ((p5 → ((p4 ∧ (p3 ∧ (True → p2))) ∨ ((p2 → p4) ∧ (p3 → p1)))) ∨ p2)) ∨ p4))) ∨ (p5 ∨ p3)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112221706654790016474627383651 : (((p1 ∨ (((p2 ∨ ((p5 → p4) ∧ ((True ∧ (p4 → False)) ∧ p1))) ∨ p4) ∧ ((p1 → False) ∨ ((True ∨ False) → p2)))) ∨ True) ∨ (p5 → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678953550447800735681205657984 : ((((p4 ∧ (((p5 ∨ p2) → p1) ∧ (p4 → ((p5 ∧ True) ∨ ((p2 → False) ∨ ((p5 → False) ∧ p5)))))) ∨ (p1 ∧ ((True ∨ False) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56469660815902230132849326287 : ((((p2 ∨ p1) → (p5 ∨ p2)) → ((((p4 ∨ (((((True ∧ p3) ∧ p4) ∧ p4) → p1) ∨ (False ∧ True))) → p3) ∧ True) ∧ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323552095738277597378965138635 : (p5 ∨ ((((True → (p4 → ((((True ∧ (False ∨ True)) ∧ p3) ∨ ((p4 → True) → p3)) → p2))) ∨ p4) ∧ (p1 ∧ p5)) → ((p2 ∨ True) ∨ False))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232908472323909528706865503175 : ((p3 ∧ (p3 ∧ p3)) → (((p2 ∨ (p4 ∨ (p1 ∨ (p1 ∨ p5)))) → ((p4 ∨ p2) → p1)) ∨ ((p2 ∨ False) ∨ (p1 → (p1 ∨ (True → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261093906851518863797391821935 : ((p4 → p3) → (((((p1 → p5) ∨ p4) ∨ ((True ∨ (p5 → p2)) → p1)) ∨ p5) ∨ ((((p1 ∧ (p4 ∧ p1)) ∨ p4) ∨ False) → (p5 ∨ p4)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40149622001809302304454356476 : ((((((((p5 ∨ p3) ∧ (p1 ∨ (p4 → False))) → (True ∧ p1)) ∧ p5) ∧ (((p5 ∨ p1) ∧ True) → (True ∨ (p4 → p1)))) ∧ p3) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251136203516500871877626698253 : ((p2 → False) ∨ ((p2 ∧ (p2 → ((False ∨ ((True → p2) → p3)) ∧ False))) → ((p4 ∨ False) ∨ ((((p2 → (p1 ∧ p3)) ∧ p2) → p3) → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171520391559854249430493518272 : ((((p3 ∨ ((p2 ∨ (True → (True → False))) → ((p3 ∧ p3) ∧ p5))) ∧ p4) ∨ True) ∨ ((p3 ∧ False) → (((p5 ∧ p1) → False) ∧ (True → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157848533344697918578947137146 : ((((p4 ∨ (p2 ∧ (False ∨ (False → False)))) ∨ (p1 ∧ p5)) ∧ ((True → ((p1 ∧ False) ∨ p2)) ∧ False)) ∨ ((p3 ∨ (p2 ∨ (True ∨ p5))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39425041536994794044241939733 : (((p4 ∧ (p1 ∨ ((False ∨ (False ∧ (((p2 ∨ p4) ∧ (True → False)) ∨ (p2 ∧ ((p4 ∨ p3) → (True → (True ∨ p3))))))) ∨ False))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156679974620835702990091255292 : ((((False ∧ ((True → ((p4 ∧ (True ∨ True)) ∧ (True ∨ True))) ∨ (False ∨ p1))) ∨ (p3 ∧ p2)) ∧ p5) ∨ ((False → (p5 → (p4 → p2))) ∧ True)) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



