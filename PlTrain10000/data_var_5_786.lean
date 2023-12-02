variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124340476597169929516721807208 : (((p4 → ((((p4 → p1) ∨ True) ∧ p4) ∧ p2)) ∧ ((((True ∨ ((p1 ∧ False) ∧ p3)) ∨ (True ∨ False)) ∨ (p1 → True)) ∨ True)) → (p2 → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185771533156488486893037419938 : ((p4 → (((p4 ∧ False) ∨ False) ∨ ((p3 ∨ p3) → (p1 ∨ p5)))) ∨ ((False → (True → (((True → p1) ∨ p1) → (p1 ∨ (p5 ∨ p4))))) ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720029973484412102982999225095 : ((((((p2 ∨ True) ∨ p2) ∧ True) → (p1 ∨ (p2 ∧ (p4 ∨ (False ∧ (p5 ∨ (((p2 → p1) ∧ (False ∨ True)) ∧ (True → (p1 ∧ p1))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305011315005170896526922698228 : (p1 ∨ (((p3 ∧ (((p4 → p4) ∧ p4) ∨ p4)) → (((p5 ∧ p2) → (((p1 → p1) → False) → (False ∧ p1))) ∨ p2)) ∨ (p4 ∧ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h13 := h8 h11
    -- False on the left can always be used.
    apply False.elim h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h7.left
    let h15 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h16 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h18 := h8 h16
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h24 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h25
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h26 := h21 h24
    -- False on the left can always be used.
    apply False.elim h26
    -- Conjunctions on the left can always be decomposed.
    let h27 := h20.left
    let h28 := h20.right
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h29 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h31 := h21 h29
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136314644750860791224633932172 : ((((p3 ∨ (False ∨ p5)) ∨ p4) ∧ (((True ∧ ((True ∧ p2) → p4)) → (p3 ∨ (p1 ∨ False))) ∨ ((True ∨ p5) → p4))) ∨ (p4 ∨ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172150808736103558398326628958 : (((((((p2 ∨ p3) ∧ p5) ∨ (p2 ∧ False)) ∨ p1) ∧ p1) ∨ (True ∨ (False ∧ p1))) ∨ (p3 → (p1 ∧ ((p2 ∧ p5) ∨ (False → (p3 → p2)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_650139461468588658129392947152 : ((((((p2 → (True → ((p2 → (False → p3)) ∨ (False ∨ (p2 ∨ True))))) → (True ∧ p1)) ∧ (((p1 ∨ p5) → p5) ∧ p2)) ∧ (p1 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39396372095310759044433808856 : (((p4 ∧ (((((((p2 → (p4 ∨ p3)) → ((p5 → (p1 ∧ False)) ∧ p1)) ∧ (True ∨ p3)) ∨ False) → (p4 ∨ True)) → False) ∨ p5)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51722033344988733837204204417 : ((((p4 ∧ ((p3 → (p3 ∨ p3)) → False)) ∨ ((p5 ∧ p1) ∨ (False → (False ∨ p1)))) ∧ (((p5 ∨ (p5 → (False → False))) → False) ∨ True)) ∨ p5) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686389275354768610479083596409 : (((((p4 → (p2 ∨ (True → p2))) ∧ (p4 ∧ ((p2 → ((p1 ∨ p5) → (p2 ∧ True))) → p1))) → ((((p1 → p5) ∧ p5) ∨ True) ∧ True)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256319508773829634659515803212 : ((False ∨ p1) → (p3 ∨ (((p5 ∧ False) ∨ ((p2 ∨ (p3 → p2)) ∨ ((p1 ∨ (p4 ∧ (((p5 ∨ False) ∨ (True ∧ False)) → p2))) ∧ False))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328551691005130165361705363942 : (True → (((True ∨ (p1 → (p3 ∧ (False ∨ ((p1 ∨ p4) ∨ (p3 ∨ p4)))))) → (True → False)) → ((p4 ∨ ((p5 → p4) ∧ (p2 ∨ False))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (p1 → (p3 ∧ (False ∨ ((p1 ∨ p4) ∨ (p3 ∨ p4)))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228518539199431020586683467959 : ((p1 ∨ (True ∧ p5)) ∨ ((p5 ∧ (p3 ∧ p1)) ∨ (((False → p2) ∨ (True ∨ ((((False ∧ p2) ∧ p1) ∧ p4) ∧ ((p3 → True) ∧ p3)))) ∨ p1))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319786966363153079122403933957 : (p4 ∨ (((False ∨ p5) ∨ (p2 ∧ (p5 → p3))) → ((False ∨ (p5 → ((p5 → ((True → p1) ∧ p5)) ∧ p4))) ∨ (p1 → (p3 → (p3 → p3)))))) := by
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173684064956698413183333967203 : ((((p4 ∨ (True ∨ (((p5 ∧ p1) → (p3 → True)) → (p1 ∧ p5)))) ∨ True) ∨ True) → (False ∨ ((True → (p1 → True)) ∨ ((p3 ∨ True) ∨ True)))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178305714518325159039835218561 : (((((p2 ∨ p1) ∧ (p1 ∨ (p1 ∧ (True ∧ p2)))) ∧ p1) ∨ (p2 → True)) ∨ (False ∧ ((((p2 ∨ p5) ∨ p1) ∧ ((True → p4) ∨ p5)) ∧ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263999200610420054189893400150 : (True ∧ ((((p3 → (p2 → (True → p3))) ∨ (p2 ∨ (p4 → p4))) ∧ p1) → ((((p5 ∧ p5) ∧ (p5 ∧ p2)) ∨ True) → (p5 → (False ∨ p1))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603251171765045120743778909277 : ((((p2 ∨ ((p5 ∧ (p4 ∧ True)) ∧ (p5 → (((((((p4 ∨ p3) ∨ p3) → False) ∧ (True → p4)) → p4) → (p1 → True)) ∧ p2)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111481006493900408485069944139 : (((p2 → ((((p4 ∧ (p4 ∧ p5)) ∨ p1) ∧ ((p4 ∧ p3) → (((p1 → p2) ∨ (p1 → p4)) → (p5 ∨ True)))) → p3)) ∧ p3) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142995649501706822087321652076 : ((True → ((((p2 ∨ (True → (p4 → (p5 → (p5 ∧ p5))))) ∧ p4) ∧ p5) ∧ ((((True → False) ∨ p3) ∨ True) ∧ False))) → ((p4 ∨ p2) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55969422039961749972645072717 : (((((p5 ∨ p3) ∨ p4) ∧ p4) ∨ (((p4 ∧ False) ∧ (p1 ∨ (True ∨ (p1 ∧ ((True ∨ (False ∧ p2)) → (p4 ∨ True)))))) ∧ (p1 ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150040559029468829639124041339 : ((p5 ∨ (p5 ∨ ((p5 ∨ (((((p4 ∨ (p3 → p2)) ∧ ((p4 ∨ True) ∧ p2)) → p2) ∨ True) ∧ p2)) ∨ p1))) ∨ ((p3 ∧ (True → False)) → False)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134870039867076615419302498714 : (((p1 → (((p5 → (p4 ∧ ((p3 ∨ (p5 → (p1 ∧ p3))) → p2))) → (p3 → False)) → ((p4 → p5) → p4))) → p1) ∨ (False → (False ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65400907932414940881449121983 : ((p3 ∨ ((False ∧ (True ∨ (p4 ∨ False))) ∧ (p3 ∧ ((p5 → (((p5 ∧ ((p5 ∧ p5) ∧ False)) ∧ p2) ∨ p2)) ∧ ((p1 → True) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213873956192153463426093400433 : (((p2 ∨ (p2 ∧ p1)) ∨ p2) ∨ ((p2 → ((False ∨ p3) → (p1 ∧ False))) → (p5 → (p4 ∨ ((False ∨ ((p2 → p2) ∨ p2)) ∨ (False → p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52549719032328451735553180051 : (((((p3 ∧ (p1 → (((False ∧ p2) → p3) ∨ p3))) → (False ∧ p3)) → p5) ∨ (p2 ∨ (p1 ∨ (False ∨ (True → ((p3 ∧ p5) ∨ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135827883414893872800540481419 : (((((p4 → (p4 → (p3 → False))) → p5) ∧ (p1 ∧ (p2 → p1))) ∧ (True ∧ ((p4 ∧ ((True ∧ p3) ∧ p5)) → False))) ∨ ((False ∧ p3) → p5)) := by
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
theorem thm_5_vars_733920499780261202522293430376 : ((((True ∨ True) ∧ ((p5 ∨ p2) ∨ (p4 ∧ (p3 ∧ ((p3 ∨ (((False ∧ ((p2 ∨ p1) ∧ p3)) ∨ (p2 → p5)) → p2)) → (p2 ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118147082748979865077858111732 : ((False ∨ (((p3 ∨ (p1 ∧ True)) ∨ (((p2 ∨ p1) ∨ p3) → False)) ∨ (p1 ∨ ((p5 ∨ ((p5 → p2) ∧ p5)) ∨ (p4 ∨ True))))) ∨ (False ∧ p1)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324261744418792423670596412996 : (p5 ∨ ((((False ∧ True) ∧ (p3 → p1)) ∨ (p5 ∧ p3)) ∨ ((p3 ∨ ((True ∧ p5) ∨ (False → (p3 → p4)))) ∨ (True ∧ (p2 ∧ (p5 ∧ p3)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807079829744485134011679412908 : (((p4 → ((True → ((p3 → ((p1 ∨ p3) → (p3 ∧ (((p4 ∧ p5) ∧ (p5 ∨ False)) ∨ p4)))) ∨ p1)) ∧ (((p3 → True) ∨ True) ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117143296340019874213995057487 : (((p5 → p5) → (p5 → ((((False → True) ∨ ((p4 ∨ (((p2 ∧ p2) ∧ p1) → (False ∨ p1))) ∧ p3)) ∧ (True → False)) ∨ p4))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147370331294144894245080912975 : ((((((p4 ∨ (p5 → p1)) ∨ p3) → (p5 → ((p3 ∨ False) ∨ p2))) ∨ ((True → (False ∧ False)) → p4)) ∨ p5) ∨ (p1 → (p4 ∧ (p3 ∧ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625928330023941952774781314083 : ((((p2 → (((p4 ∧ ((p5 ∧ False) ∧ ((False ∨ ((((False ∨ p4) ∨ False) → p5) ∨ (True → p5))) → p5))) ∧ False) ∨ (False → True))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185586622381662002285977641213 : ((p5 ∨ (((True → (p2 ∨ p5)) ∧ (p4 ∧ False)) ∨ (True → True))) ∨ ((((p1 ∨ p2) ∨ p2) → (((p1 ∧ p1) → (False ∨ p2)) ∨ p3)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137524677885963865923742131709 : ((p5 ∧ ((p1 → p1) → ((((((False ∧ (False ∨ (p1 ∨ (True ∨ True)))) ∨ False) ∨ p2) → (True → False)) → p1) ∧ p3))) ∨ (p3 → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157586989530716811782712436754 : (((p4 ∧ (((True ∧ True) → ((p1 ∧ False) → ((True ∧ p2) → p2))) ∨ (p1 → False))) → (True → p1)) ∨ (p2 ∨ ((False → (False → p4)) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209090466697235656138180410367 : ((p2 ∨ (((p2 ∧ p1) → p1) ∨ p4)) → ((((((True ∧ p3) → p4) → (((False ∨ True) → p3) ∧ p5)) → (False ∧ p4)) → (p2 ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_64437418147605474354513039383 : ((p1 ∨ ((((p4 ∧ (False ∨ ((p3 → (p3 ∨ (((False ∧ False) ∧ p5) → ((p2 ∧ p2) → p1)))) ∧ p1))) → p2) → p3) ∨ (True → True))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156802367110995876412500728375 : (((p5 ∧ (p1 → ((p2 → (p5 ∨ (((True ∨ p1) → False) ∧ ((True ∧ False) ∨ p3)))) ∧ p1))) ∧ p2) ∨ (p3 → ((p4 ∨ (p2 ∨ p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67507411503324602784332664082 : ((p1 → (((p3 ∧ ((True → (p2 ∨ False)) → p4)) → p2) ∨ (((p1 ∧ (False → (p3 ∧ p5))) → ((p3 ∧ (p3 → p1)) ∨ p1)) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246460837457663102516324588923 : ((p5 ∧ False) ∨ (((p5 ∧ False) ∧ (((True ∨ p5) ∧ p1) ∨ p4)) ∨ ((p3 → ((p5 ∨ p2) → ((p4 ∧ p5) → p3))) ∧ ((p2 → True) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329678455511167506353165294827 : (True → ((p1 ∨ p3) → (p3 ∨ (p5 ∨ (((((True ∧ (p2 → (p1 → True))) → p3) ∨ p4) ∨ (p1 ∨ p1)) ∨ (True ∧ ((p2 ∧ p1) → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263892894679572359716312592354 : (True ∧ ((((p2 ∧ (p5 ∧ (False ∧ p5))) ∨ p1) ∧ (p5 ∧ ((p2 ∧ p3) → False))) ∨ ((False ∧ p2) → (((p1 ∨ p4) → p3) ∨ (False ∧ True))))) := by
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
theorem thm_5_vars_249679888468032231981229013239 : ((p5 ∨ p4) ∨ ((((p2 ∨ True) ∧ (False → p2)) ∨ (p5 ∨ True)) → (((p5 ∧ p2) → ((p5 ∨ p1) ∧ (False ∧ p3))) ∨ ((True ∨ p2) ∨ p4)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_811184317914530359237857728883 : (((p5 → (p3 ∧ (p5 → (True ∧ (p3 ∧ (p5 → ((p4 → (p3 ∧ (False ∨ p5))) ∨ (((p2 ∧ (p1 → False)) ∨ p4) ∧ (True ∧ p4))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231550810404104315969219864023 : (((p5 → False) ∨ False) → (((((((p4 ∨ (p3 ∨ p5)) ∧ p1) → (p5 ∧ p1)) ∨ ((p1 → p1) ∧ False)) ∨ p2) ∨ p5) ∨ (True ∨ (p3 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173216824043973242869539804832 : ((p5 ∨ (p2 ∧ ((((p2 ∨ p1) → ((p1 → (p5 → True)) ∧ p5)) ∨ p5) ∧ p1))) ∨ ((False → (p4 ∧ ((p2 ∧ (True ∨ p4)) ∨ p5))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_25512566217927871913560301642 : (((p1 ∨ (p3 ∨ p1)) → (((p4 → (((p5 → (False ∨ p1)) ∨ False) ∨ p4)) ∨ True) ∨ ((p1 → (((p5 → p3) → p4) ∨ p4)) ∧ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50329332545997429720018799320 : (((((p5 ∨ p2) ∨ (False ∨ ((False ∧ True) → False))) ∧ (p4 ∧ ((False → (p2 ∧ p5)) ∧ (True ∧ p4)))) ∨ (p3 → (True ∨ (True ∧ p1)))) ∨ p2) := by
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
theorem thm_5_vars_694596710330182326826765609780 : ((((p4 ∧ (((p5 ∧ False) ∨ ((p3 ∨ (p2 → (False ∨ p2))) ∨ p4)) ∨ True)) ∨ ((p4 → (((True ∧ False) ∨ p5) ∨ (True ∨ p5))) ∨ p3)) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65460066112409778548540735274 : ((p3 ∨ ((False → True) → ((((p2 ∨ p5) ∨ p2) ∧ ((p2 ∧ p1) ∧ (((p3 → (p2 → True)) → (p1 → p4)) ∨ (False ∧ p2)))) → p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h4.left
      let h8 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : (p3 → (p2 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h15 := h11 h12
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- False on the left can always be used.
        apply False.elim h19
    case inr h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h4.left
      let h23 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h24 := h22.left
      let h25 := h22.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h26 =>
        -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
        have h27 : (p3 → (p2 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h28
          -- Implications on the right can always be decomposed.
          intro h29
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h26, we can now drive its conclusion.
        let h30 := h26 h27
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h33 =>
        -- Conjunctions on the left can always be decomposed.
        let h34 := h33.left
        let h35 := h33.right
        -- False on the left can always be used.
        apply False.elim h34
  case inr h36 =>
    -- Conjunctions on the left can always be decomposed.
    let h37 := h4.left
    let h38 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h41 =>
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h42 : (p3 → (p2 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h43
        -- Implications on the right can always be decomposed.
        intro h44
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h45 := h41 h42
      -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
      have h46 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h40
      -- We have shown the premise of h45, we can now drive its conclusion.
      let h47 := h45 h46
      -- One of the premise coincides with the conclusion.
      exact h47
    case inr h48 =>
      -- Conjunctions on the left can always be decomposed.
      let h49 := h48.left
      let h50 := h48.right
      -- False on the left can always be used.
      apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241744011613910452094828229465 : ((p1 → True) ∧ (p2 ∨ ((p4 → p3) ∨ (((((p3 ∧ (True ∨ False)) → (((p3 → p2) → p4) ∧ p2)) → (p2 → (p1 → p4))) ∨ p4) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636265563961913480044160651486 : (((((p2 → ((((p3 ∧ True) → p1) ∨ ((True ∧ True) → ((p2 → p2) → p2))) ∨ p5)) ∨ (p4 ∧ ((p1 ∨ p1) ∨ (p4 ∧ p1)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336207006978316253438980360349 : (p1 → (((((True ∨ ((((p4 ∨ p1) ∧ p3) → ((p5 ∧ (True ∧ p1)) → (p4 ∨ p4))) ∧ True)) ∨ (p1 ∨ False)) ∨ p4) → (True → p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68695427734426376954595158888 : ((p4 → ((p1 ∨ ((((True ∧ p1) ∧ ((p2 ∨ (False → (((False → p3) → False) ∨ p3))) ∧ p5)) ∧ p1) ∧ (p2 ∧ False))) ∨ (False ∨ True))) ∨ p1) := by
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
theorem thm_5_vars_72395071540110727126884580103 : (((((((False ∧ (p4 → p5)) ∨ (p5 ∨ (p5 → ((p1 ∧ p4) ∨ p5)))) → (((True → False) ∧ (p4 → p3)) ∨ p2)) ∧ True) ∧ p1) ∨ p2) → p2) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ (p4 → p5)) ∨ (p5 ∨ (p5 → ((p1 ∧ p4) ∨ p5)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47807017888276642390290895398 : ((((((True → (((p1 → (p4 → (((p2 ∨ p5) ∨ (p1 → p2)) → p2))) → p1) ∧ True)) ∨ False) → (p5 → False)) → p5) → (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327430946423899090291305390474 : (True → (((True → ((((p2 → (p1 → p1)) ∧ ((True ∨ False) ∧ (False ∨ False))) → p2) ∧ False)) ∧ (((p1 ∨ p4) → p4) → (p2 → True))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343209400903244939419014239219 : (p2 → (((True → p2) ∨ p2) → ((((((False → (p3 ∧ p5)) ∧ True) ∨ True) ∧ p3) ∧ (((p1 ∨ p3) ∨ (p5 ∧ p1)) → True)) → (p3 ∨ p1)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158956158644319398433289355679 : ((p2 ∨ (p3 ∧ (((False → True) ∧ (p3 ∨ ((p1 ∨ (True ∨ ((p4 → True) ∨ False))) → p1))) ∧ True))) ∨ ((False → p4) ∧ ((p2 → p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690068163362386922511190905924 : ((((p5 ∧ ((p2 ∧ ((p4 → ((p5 → True) → p3)) ∧ ((p3 ∧ p4) ∨ p3))) ∨ p3)) ∨ (((True ∧ p4) ∨ ((p1 ∨ p1) ∨ p5)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708688410341532976493339631339 : (((((((p2 ∧ (False → True)) ∧ False) → p1) → p1) → ((((p4 ∧ ((p3 ∨ p2) ∨ (p2 ∨ p4))) → (p2 → False)) ∨ (p2 ∨ p5)) ∨ p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ (False → True)) ∧ False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806306218687094113826462492448 : (((p4 → (((p2 → (p5 ∨ p5)) ∧ (p1 ∧ ((p1 → (p5 ∧ (p1 ∨ p2))) ∨ ((((p3 ∨ True) → False) ∧ False) ∨ (p5 ∨ p2))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306158378628007520615624912176 : (p1 ∨ (((p5 ∨ p2) ∨ p3) ∨ ((((p1 → ((p2 ∧ (True → p3)) → ((True ∨ ((True → False) ∧ p2)) ∨ True))) ∨ p4) → (p2 → p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199394135302884423054357376144 : ((((p2 ∧ p1) ∧ (p4 → (p1 ∧ p2))) ∨ p2) → (False ∨ (((False ∧ p4) ∨ p3) ∨ ((((False ∨ True) ∧ (p5 ∨ p5)) ∧ p2) → (False → True))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145155034751566693457576029943 : ((((p3 → True) → ((p3 ∨ ((False ∧ True) ∧ False)) ∧ p2)) → (p5 ∨ ((False ∨ (p4 ∧ (p5 → False))) ∨ True))) ∧ (True ∨ ((True → False) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_64778447485488503008981881388 : ((p2 ∨ ((((p1 → (((p5 ∨ p3) ∧ True) ∨ ((p2 → ((p3 ∧ (((True → p2) ∧ p1) → False)) ∨ p1)) ∨ p1))) ∨ p4) → p2) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260500995606513408025492448424 : ((p3 → False) → (True ∧ (((((True ∧ ((((True → p5) → (p5 ∧ (p3 ∧ p4))) ∧ p1) ∨ (True ∧ p1))) → p1) ∧ True) → (True ∧ p1)) ∨ True))) := by
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
theorem thm_5_vars_115801848064324773532271282041 : (((((True ∨ p2) ∧ False) → p2) ∧ ((True ∧ ((((p5 ∧ ((False → p2) → False)) → (p3 ∨ (False ∧ p3))) → False) ∨ p5)) ∧ p5)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119337254158930547537124732059 : ((p3 → (((p1 ∨ False) ∨ (False ∧ p1)) ∨ (p1 ∧ (p3 → ((p3 ∨ (((p1 ∧ (p4 → (False → True))) → True) ∨ p3)) ∧ True))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614392914452498645354587332265 : (((((p2 ∨ (((p2 ∨ ((False ∧ p5) → (True ∨ ((p5 ∧ True) ∨ (True ∧ p4))))) ∧ p2) ∨ (True → True))) → (p5 ∧ (p1 ∧ p4))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228827873548043494143148886163 : ((p3 ∨ (p5 ∨ p5)) ∨ ((p3 ∧ True) → ((((p1 ∨ (p1 → False)) ∧ (True ∧ True)) → ((p4 → p3) ∧ (p1 → ((p4 ∨ p1) → p5)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_52456225040620831356824105747 : (((p5 ∧ ((p1 → p2) ∧ (p3 ∨ ((p2 ∨ p3) ∨ ((True ∧ p4) → False))))) ∧ (p1 ∧ ((True ∨ p3) → ((p3 → (p4 ∧ p4)) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352721580069748849720337318355 : (p4 → ((p2 → p5) ∨ (((p2 ∨ (p2 ∨ ((((p3 ∨ (p1 ∧ False)) ∨ (p2 → (False ∧ p2))) ∧ (p1 ∧ False)) ∨ (p1 ∨ False)))) ∨ p4) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143013607444467786654088836623 : ((True → ((p5 → True) → ((p1 → ((p2 → (((True → False) ∧ (p3 → ((p2 ∧ p5) ∨ p1))) → p5)) → p2)) ∧ p2))) → ((True → p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790491083840154500227549343701 : (((p5 ∨ (False ∨ ((p2 ∧ (((p1 ∧ p5) ∨ (p1 ∧ p3)) → (p4 → (p4 ∨ p3)))) ∨ ((p5 → (False ∨ ((p3 ∨ p3) ∨ p3))) → p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158338292382051309539222877178 : (((p2 ∧ False) ∧ (False ∨ (((p4 ∨ p2) ∨ p5) ∨ ((p5 ∨ ((True ∧ (False → p3)) → p4)) ∨ p4)))) ∨ (((p3 ∧ True) ∨ p1) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761792441156889946223381012387 : (((p3 ∧ (((((p4 → (p5 ∨ p1)) ∨ p3) → (((False ∧ p2) ∨ ((((False ∨ p3) ∧ p2) ∧ p2) → p3)) ∧ (False ∨ True))) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358489158924564021988310949688 : (p5 → (p1 → ((p4 ∨ (p5 → True)) ∧ ((((False ∨ p3) → p2) → p3) ∨ (((False ∨ ((p4 → True) ∧ True)) ∨ (False → p2)) ∨ (True ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197305477739559500542352343111 : ((((p2 ∨ p5) ∧ ((p4 ∨ p2) ∨ p2)) → p5) ∨ ((p5 ∨ ((p3 ∧ ((p4 ∧ p1) → p5)) ∨ ((False → ((p2 ∧ p2) → p4)) ∨ p1))) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261103331028489328408246221025 : ((p4 → p3) → ((True → (p2 ∨ p2)) → ((p2 → (((p3 ∧ p4) ∨ (True ∨ (True ∨ (p4 → p2)))) ∧ (False → (p4 ∧ p5)))) ∧ (p2 ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166497781311141133739428740123 : ((p3 ∨ (p1 ∨ (((True ∧ p4) → ((((p2 ∨ p5) ∨ p1) ∧ (p1 → p4)) ∧ True)) ∨ p5))) ∨ ((p1 ∨ (((p3 ∨ p2) ∧ p5) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_255530789890251742696543745226 : ((p5 ∧ p2) → (p4 ∨ (((p5 → ((p1 ∧ ((((((p5 ∨ (p2 → p3)) → p3) ∧ p5) → False) ∧ p5) ∨ True)) ∨ (p3 ∧ True))) ∨ False) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311190463491769431665264108048 : (p2 ∨ ((p2 ∨ p2) → (((((((((False → (p2 ∨ p2)) ∨ p2) ∨ p5) ∨ True) ∧ (p1 ∨ (p3 ∨ True))) ∨ (p3 ∨ False)) ∨ p1) ∨ False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339624936947947929012306285147 : (p1 → (p2 ∨ ((((p3 → (False ∧ p1)) ∨ ((p2 → (p5 ∧ False)) → p2)) ∧ p5) ∨ ((((p3 ∧ (p3 ∧ True)) ∧ p3) ∨ (p2 ∧ p4)) ∨ True)))) := by
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
theorem thm_5_vars_149388368820912141361617671248 : (((p5 → p1) → ((p4 ∧ (p5 ∧ ((((p2 ∧ ((p3 ∨ p1) ∨ p3)) ∧ p1) ∧ p2) ∧ (p2 ∧ p5)))) ∨ True)) ∨ (p5 → (p1 → (True ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113491611989312578069860606921 : (((((((((p5 → ((p4 ∧ False) → True)) ∨ (p3 ∨ p1)) ∨ p4) ∧ p2) → False) ∨ p1) ∧ (p2 ∧ (p4 ∨ p2))) ∨ (p2 ∨ p4)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148371454784930280775348319157 : ((((p4 ∧ ((p1 → True) → ((p2 → ((True ∨ p2) → p1)) → True))) ∨ p3) ∨ ((p1 ∨ (True ∨ p2)) → p3)) ∨ (p4 ∨ (p1 ∨ (p2 → True)))) := by
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
theorem thm_5_vars_337113443617662031193589497236 : (p1 → (((p4 ∧ p4) ∨ (((p3 ∨ ((True → (p1 ∧ False)) ∧ p2)) → p2) ∨ (((p2 → (p4 ∧ p4)) ∨ (p5 ∧ False)) ∧ p1))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300375279777120332567923262460 : (False ∨ (((p1 ∧ (((p2 → (p3 ∨ (True ∧ p4))) → ((p1 ∧ p5) → ((p1 → p2) → p4))) ∨ p4)) → (p5 → p3)) ∨ ((False ∧ p4) → p1))) := by
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
theorem thm_5_vars_791335541142210071655753419174 : (((True → (((p2 → (p4 ∧ (p2 → (((p1 ∧ ((False → (p4 ∧ p2)) ∧ True)) ∨ (p3 ∧ p5)) ∨ ((p4 ∧ p5) ∨ p2))))) → p1) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_617459577331613000744603362771 : ((((((p4 → ((p1 ∧ False) → False)) ∧ p2) ∧ (((p4 → p2) → (p1 ∧ (p2 ∨ (p4 ∨ (p5 ∧ ((p2 → p3) ∧ False)))))) → False)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305298127845026861124329232123 : (p1 ∨ (((((p4 → False) ∨ p4) → ((p3 ∨ p4) ∨ (p1 → ((False → p2) ∧ p1)))) → (p1 ∧ p5)) ∨ (p3 → (p4 ∨ ((p4 ∧ p4) → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204383097421558914881196195394 : (((p5 ∨ (False ∨ (p2 ∧ p3))) ∧ p5) ∨ (((p4 ∧ ((((True ∧ (p2 ∧ p5)) ∧ False) → p3) ∨ (p3 ∧ p2))) → True) ∨ (p3 ∧ (p4 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149342739138112893977012701200 : (((p2 ∨ True) → ((p2 ∨ ((p2 → (((p1 → (p1 ∨ p2)) ∨ p2) ∧ p1)) ∧ p1)) ∧ (p3 → (p2 ∧ False)))) ∨ (((p4 ∨ p3) ∧ False) → p5)) := by
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
theorem thm_5_vars_150005685143272954986254075353 : ((p5 ∨ (((p3 ∨ ((p3 ∨ p1) ∧ p2)) ∧ (((p3 ∧ True) ∨ ((p2 → (False → p5)) → p5)) → p2)) ∨ p5)) ∨ (True ∨ (p3 → (p4 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151557389033564642971669247289 : ((((p3 ∨ ((((((False ∨ p3) ∨ (p2 → p4)) ∨ p5) ∧ (False ∧ False)) ∧ p1) → p3)) ∨ p2) → (p1 ∧ p5)) → (p2 → (p5 ∧ (p5 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p3 ∨ ((((((False ∨ p3) ∨ (p2 → p4)) ∨ p5) ∧ (False ∧ False)) ∧ p1) → p3)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 ∨ ((((((False ∨ p3) ∨ (p2 → p4)) ∨ p5) ∧ (False ∧ False)) ∧ p1) → p3)) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178230524315926618507161908337 : (((p3 → ((False → (p3 ∧ (((p3 ∨ p1) ∨ p5) → p5))) ∨ p1)) → False) ∨ ((True → (((False ∨ p4) ∨ p2) ∨ (p3 → p3))) ∨ (p2 ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49417662085067170796509083938 : ((((p5 ∨ (((False ∧ (p2 ∨ (p2 → p1))) ∨ (((((p5 → p2) ∧ p5) → False) → False) ∧ p5)) ∧ p4)) ∧ p4) → (False ∧ (p2 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



