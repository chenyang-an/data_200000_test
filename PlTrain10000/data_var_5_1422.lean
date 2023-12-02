variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74088553069760297172212926024 : (((((p2 → (True ∨ False)) → p3) ∧ (((((p2 ∧ ((p4 ∨ True) ∨ p5)) → p3) ∧ ((p1 ∧ (p4 ∧ p4)) ∨ p5)) ∧ p3) → p1)) ∨ False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 → (True ∨ False)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50508430504425515819700088761 : (((((p5 ∨ (p2 ∨ ((p5 → ((p5 ∧ True) ∧ False)) → (p3 → p1)))) ∨ ((p5 → True) ∨ p1)) ∧ p4) → (p2 ∨ (p4 → (p3 ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149844011691701543455786578822 : ((p1 ∨ ((True ∧ True) → (((((p5 ∨ ((p5 ∨ p3) ∨ True)) → p3) ∧ p1) → (False ∧ True)) → (p5 ∧ p1)))) ∨ ((p1 → p5) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43759622087458236011783146983 : ((((p2 ∧ ((((False ∨ p1) → (p4 → True)) ∧ (p5 ∧ (p2 → (p2 → p1)))) → (p1 → (True ∨ (p4 ∧ (True → p3)))))) → p3) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320444372872333908161967306258 : (p4 ∨ ((p3 ∨ p4) → (False ∨ ((p1 → ((p5 ∧ p5) → ((p3 ∨ p5) ∨ (p2 → ((p2 ∧ (p5 ∧ p4)) ∧ False))))) ∧ ((p4 ∧ p4) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313956532377282355898594829161 : (p3 ∨ (((((False ∨ p4) ∨ (p2 ∨ p5)) → (p1 ∧ (((p1 ∧ False) ∨ p4) ∧ (((True ∨ p4) ∨ p4) ∨ False)))) ∨ (False → False)) ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123495042300987218552590142971 : ((((((((False → (p5 → (p3 → p5))) ∨ p3) → False) → True) → p2) ∨ (p4 ∨ p1)) ∧ (p5 ∨ ((p2 ∨ p5) ∨ (True ∧ p1)))) → (p4 ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h19 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- Disjunctions on the left can always be decomposed.
          cases h26
          case inl h27 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h28 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686236217998554043729786361036 : (((((p2 → (((False ∨ (False ∧ (p4 ∧ p5))) ∨ p3) ∨ p3)) → (False ∨ ((True → p1) → p3))) → (p5 ∧ (p5 → (False ∨ (True ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115065735403270243036573206352 : (((((p4 → (True ∨ p4)) ∧ p3) → (((p2 ∧ p4) ∨ p2) ∨ p4)) ∨ ((p4 → (p1 → (p3 → (p3 ∧ (p5 → p1))))) → True)) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49960399845067752117190721496 : ((((True ∨ ((p4 ∨ ((p3 ∧ ((p2 ∧ ((p1 ∨ p5) ∨ p5)) ∨ p2)) → p4)) ∧ p5)) → (p5 → p3)) ∧ ((p2 ∨ (p1 ∧ p4)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136278652811912680160808974189 : ((((p1 ∧ (p2 ∨ p2)) → (False → p2)) → ((False ∨ (((p5 ∧ ((p2 → p4) ∧ p3)) ∨ p4) ∧ (False → p4))) → p1)) ∨ (True ∨ (p3 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148921823188992531808838695859 : (((((p1 ∨ p3) → p2) → p4) → (((p2 ∨ ((p5 → (False ∨ (False ∨ p2))) ∧ p2)) ∧ (p1 ∨ p3)) ∨ p2)) ∨ (p4 → ((p3 ∧ p4) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134330947513396019812962241679 : (((p3 ∧ ((p1 ∨ ((p3 ∨ (p3 ∨ (True ∨ p4))) ∧ (p3 → ((p1 ∨ p2) ∨ (p4 ∧ (True → p1)))))) ∨ True)) ∨ p2) ∨ ((True ∨ p1) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721774360586137269036614361478 : ((((p2 ∨ ((True ∨ p5) ∨ True)) → ((p2 ∧ (p2 ∨ ((True ∧ (p3 → True)) ∧ (p4 ∧ (p1 ∨ (True ∨ (p5 ∧ p2))))))) ∧ (p4 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255077096849759200558317473556 : ((p4 ∧ p2) → (((False ∧ ((p4 ∧ ((((p1 → (p3 → False)) → False) ∨ p1) ∧ (p3 ∧ p3))) ∧ p1)) ∨ p3) ∨ ((p3 ∨ (p1 → p1)) ∨ p4))) := by
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
theorem thm_5_vars_230280853552789798382591169841 : (((False ∨ p5) ∧ p1) → (((((p1 → p5) ∨ p3) ∨ ((p1 → ((p5 → p4) → True)) ∧ p2)) ∨ p2) → (((p1 → p5) → p3) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h1.left
        let h7 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h8
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- One of the premise coincides with the conclusion.
          exact h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h1.left
        let h13 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h1.left
      let h21 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h1.left
    let h27 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- One of the premise coincides with the conclusion.
      exact h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172100518386882431127674650300 : (((p1 ∨ (((p1 → (((True → p3) ∨ p4) → False)) ∧ True) → True)) → (p5 ∨ p5)) ∨ ((False → p5) ∨ (((True → (p5 ∧ p2)) → p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47816033977037331808890468612 : ((((((((False ∧ (p5 ∨ False)) → True) ∨ True) ∨ (p3 → (p3 ∧ p3))) ∨ ((True → ((False ∨ True) ∧ True)) ∧ p2)) → p4) → (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213838052890320656618463668491 : (((p5 ∧ (p3 → p5)) ∨ p3) ∨ (((p1 ∨ ((False ∧ p3) ∨ p2)) → ((p4 ∨ p1) ∨ (p3 → p1))) ∨ (p2 → ((p1 → (p1 ∨ p4)) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53202109211053912656910428848 : (((((((p1 → p1) → (p2 → p3)) ∧ p4) → p1) → (p5 ∨ p1)) ∨ ((True ∧ (((p5 ∧ (False ∨ p4)) ∧ p5) → p5)) ∨ (p4 → p2))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200682632661972891859359296974 : ((p2 ∧ (((p2 ∨ (p3 ∧ False)) ∨ p3) ∧ p5)) → ((False ∧ ((False ∨ (((p5 ∧ True) ∧ p5) → p4)) → (p1 ∨ ((False ∨ p5) → p3)))) ∨ p5)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482184983063225232315531961031 : ((((((p3 ∨ (p1 ∨ False)) ∧ (p4 → True)) → p1) → (((p4 → (p3 ∧ (p3 → ((p3 ∧ True) → ((p1 ∧ False) ∧ p4))))) ∧ p4) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_479949586921719019844554014500 : ((((p4 ∨ ((p1 ∨ ((p1 → p3) ∨ True)) ∨ False)) ∧ (p5 ∨ ((False ∨ (((p3 ∨ False) ∨ True) → p1)) → (p2 → ((p4 ∨ p1) ∧ p1))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 ∨ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((p3 ∨ False) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184623761044210730280370806922 : ((((p1 ∨ p1) ∨ ((p5 ∨ p2) ∧ False)) ∧ ((True → p3) ∨ False)) ∨ ((p4 ∨ (((p4 ∧ False) ∨ p2) ∧ p5)) ∨ (((False → True) → p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49365431126552877379214388280 : (((p3 → (p2 ∨ ((p1 ∨ (p1 ∨ p1)) ∨ (((((p3 ∧ p3) ∨ p4) → (p5 ∧ p4)) → p3) ∧ (p1 ∨ p3))))) ∨ (p5 ∨ (p3 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149403034197817289988904769712 : ((True ∧ (((False → (False → p5)) ∨ ((p4 ∨ p4) ∨ (p3 → (p4 ∧ ((p4 → p2) → (p3 → p3)))))) → p1)) ∨ (True ∨ ((p3 ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339505228675149099879473876113 : (p1 → (False ∨ ((((((p4 ∨ False) → p4) ∧ p3) ∧ (p3 → p1)) ∨ p2) → ((p1 → False) → (True ∧ (p5 → ((False ∨ p4) ∨ (p3 → p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212286775915181378278007580300 : ((p1 ∨ ((p2 ∧ False) ∨ True)) ∧ ((p1 ∨ (p5 ∧ ((((p4 → p5) ∨ p5) ∧ (p1 ∨ (p1 ∨ p5))) ∧ (p4 ∧ (True ∨ (False ∧ False)))))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314538657718910309245222319348 : (p3 ∨ (((((((((False → p1) → False) ∨ False) ∨ p4) → (p3 ∨ (p5 ∨ p4))) → p4) → p3) → p3) ∨ ((p3 ∨ p4) → (False → (p2 → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_690872734840587755352806715386 : ((((((((p5 → ((p1 ∨ False) → p3)) ∨ p5) ∨ (p5 ∧ p3)) ∨ True) ∧ (p2 ∧ p3)) → (p4 ∨ ((p1 → True) ∧ (p4 ∨ (True ∨ p1))))) ∨ False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h3.left
        let h8 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h3.left
        let h12 := h3.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h3.left
      let h18 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h3.left
    let h22 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h23
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126505058096627029588681224483 : ((p2 ∧ ((p1 ∨ p3) ∨ ((p5 ∨ (p1 ∧ ((True → p2) ∨ False))) ∨ ((p3 → True) → ((p4 ∨ (False → p5)) → (p1 ∧ p3)))))) → (False ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61222818232735046884917416251 : ((False ∧ (False ∧ (p5 ∨ ((p4 ∨ True) → (((((p1 ∧ p1) ∨ (p4 ∨ True)) ∨ (p5 → p2)) → (p4 ∧ p1)) ∨ ((p1 ∧ p3) ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175195184805178681321431807516 : ((False ∨ ((True ∨ ((p1 ∧ (False ∨ (p4 ∧ p4))) ∧ (p3 → (False ∨ p2)))) → p4)) → (((((p1 → p3) ∨ p3) ∨ True) → p5) ∨ (True ∨ p3))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301436502121696142206659837946 : (False ∨ ((p3 ∧ (p3 ∧ (p2 ∨ p3))) → (((False ∨ (p4 ∧ (p2 ∨ p3))) ∧ ((((False ∧ p4) ∧ p5) ∧ p3) → (p2 ∨ (True ∨ p4)))) ∨ True))) := by
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
  cases h5
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
theorem thm_5_vars_315469151926056807553241020041 : (p3 ∨ (((p2 ∨ p4) ∨ False) → (False ∨ (False ∨ (p2 ∨ (((p1 ∨ True) ∧ p3) → (p3 ∨ ((((False ∧ p3) ∨ True) → (p2 ∨ p3)) ∧ p2)))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657138696237263712813449352279 : ((((((p5 → True) → p2) ∨ ((p5 → ((((((True ∧ (True → p3)) ∨ True) ∧ True) ∧ p1) ∨ (True → True)) → p5)) ∧ p4)) ∨ (p3 → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177713680131873038440267953434 : (((((p5 → ((True ∧ p2) ∧ p2)) → p1) ∨ (p5 ∧ (p1 → p2))) ∧ False) ∨ (p3 → ((((p3 ∧ p2) ∨ (p2 → (True → False))) → p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347297230481066132602181183535 : (p3 → ((p2 ∨ (p4 ∧ (((False ∧ p5) ∧ (False ∨ False)) ∨ False))) ∨ ((p2 → (False → False)) → ((p5 → ((p4 ∧ p3) → True)) ∨ (p3 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798029482130607951161199759644 : (((p1 → ((False ∨ ((((((p3 ∨ p5) → p3) ∧ ((False → p4) ∧ p4)) → (p1 → (True ∧ p5))) ∨ True) ∨ False)) ∧ ((p4 ∧ p2) → p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264085039918748966829196377660 : (True ∧ ((p1 → ((p5 ∧ p1) ∨ ((p3 ∨ p2) → (p5 ∨ p4)))) ∨ (p3 → (p3 ∨ (((p5 → ((p1 ∧ (p5 → p3)) ∧ p3)) → True) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776487178186903715573187482504 : (((p1 ∨ (((p5 ∧ (p4 ∨ (((p1 ∨ ((p5 → p1) ∨ p2)) ∨ p1) ∨ ((p5 ∨ p1) → (p3 → p4))))) ∨ (p5 → (p5 ∨ p2))) ∨ p3)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257705296278525090124226533468 : ((p3 ∨ p3) → ((True → p5) ∨ (((((False ∧ (p1 ∧ (p3 ∧ True))) ∨ (p1 → p5)) → (p5 ∨ p2)) ∨ ((p2 → p5) → (p5 ∨ p3))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114253890763755658998245776886 : (((p1 → (((((p5 → ((p1 → (False → p5)) ∨ p3)) ∨ p3) ∨ ((p1 → True) ∧ p2)) ∧ False) → False)) → ((p4 ∧ p3) ∧ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753662446377852162804053539649 : (((False ∧ ((((((True ∧ False) ∨ (p2 ∨ True)) → (True ∧ True)) ∨ (p2 ∧ p2)) → p2) ∧ (p4 ∧ ((p5 ∨ p1) ∨ ((False ∨ p4) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55405791206592270734780820582 : ((((((p3 ∨ False) → p5) ∨ p3) ∨ p1) → ((False ∧ ((True ∧ p3) ∧ (p2 ∧ ((((p4 ∨ False) ∧ (p3 ∨ p3)) ∨ False) ∨ p4)))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156829387963518671046298524732 : (((True → ((((p4 ∧ p2) ∨ ((True ∧ p5) → (p4 ∨ p5))) → False) → (p1 ∧ (False ∨ False)))) ∧ p1) ∨ (p5 ∨ (p5 → (p1 → (True → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301052902561463621693611979513 : (False ∨ (((p3 ∨ (((p4 ∨ False) ∧ p2) ∧ p3)) ∨ (p1 ∧ False)) ∨ ((((p5 ∨ (True ∧ (True ∨ False))) ∧ (p5 → p4)) ∨ (p1 → p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158559680248735018004487159575 : ((True ∧ (((p5 → p2) ∧ (((False ∧ True) → (p3 ∨ p3)) → (((p5 → False) ∧ p4) ∨ True))) ∨ p4)) ∨ (False → (True ∧ ((p3 → True) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158403336366661724043871508464 : (((True ∧ p1) ∨ ((p1 ∧ ((p1 → ((p2 ∨ ((p5 ∨ p2) → p5)) ∧ (p3 → False))) → p4)) ∧ p4)) ∨ ((p5 ∧ p4) → (p1 ∨ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177627741676870241619017950865 : (((((((p2 ∧ (p3 ∧ p3)) ∧ True) → (False → p1)) ∨ False) ∧ p3) ∧ False) ∨ ((p1 ∧ (True → ((p1 ∧ p1) → (p2 ∨ (p2 ∧ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133730231322156611459107045815 : ((((((p4 ∨ p2) → ((True ∨ True) ∧ (p5 ∨ p5))) → p5) ∧ (p1 ∧ (True ∨ ((p5 ∨ p1) ∨ (p4 ∧ p5))))) ∧ p3) ∨ ((p5 → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263905887000722987957302495011 : (True ∧ ((p5 ∨ (((p4 ∨ (p2 ∧ (p5 ∧ ((p4 ∨ True) ∨ True)))) ∧ p4) ∨ p2)) ∨ (False → ((p3 ∧ False) ∨ (False → (p4 → (p2 ∨ False))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198188549917788822257812333199 : (((False → True) → (p2 ∨ ((p3 → p2) ∨ p2))) ∨ ((p3 → ((True → p3) ∨ ((((True ∧ p3) ∨ False) → True) → p5))) ∨ (False ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54360236662851775211134997173 : (((p4 ∨ (((p1 → p3) ∧ p1) → (p3 ∧ p5))) ∧ (((((p3 ∧ False) → p1) ∨ (p4 → (p3 ∨ (p2 → (p3 → False))))) → p2) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49764702773625093735655277557 : (((False ∨ ((p2 ∨ p1) ∧ (((True ∨ False) ∧ p1) ∨ ((((p3 ∨ (False → p3)) ∧ p5) ∨ (p3 → p4)) → p4)))) → ((p1 ∧ p3) ∨ True)) ∨ p5) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- False on the left can always be used.
          apply False.elim h18
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136841012488280082256505296248 : (((p2 ∧ p2) ∨ ((False ∨ ((p1 ∧ (False ∧ (False ∨ (True ∨ p2)))) ∨ p5)) ∨ (p4 → (p1 ∨ (p1 → (p4 → p4)))))) ∨ (p2 ∧ (p5 ∨ False))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50929300746112998253587290699 : ((((True → ((p2 ∨ (p1 → (p4 ∧ p5))) → (p4 → (p3 ∧ False)))) ∨ (p1 → (p3 ∧ p3))) ∧ (((p4 ∨ (p1 ∨ p5)) ∧ True) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134345391607532032347283519416 : (((p5 ∧ ((False → (((p2 ∧ p1) ∨ True) ∧ (False ∨ p2))) ∧ (False ∨ (((p5 ∧ p1) ∧ p1) ∨ (p4 → p2))))) ∨ p1) ∨ ((False ∨ False) → p4)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319458220232503250780760311327 : (p4 ∨ (((p5 → (((p3 → True) → p1) ∧ p5)) ∨ (False ∧ (p3 ∧ p2))) ∨ (((p5 → p5) → p1) → (((False ∨ True) ∧ True) ∨ (False ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222361657211454854843007184388 : (((p2 → p4) → True) ∧ (((p2 → True) → (p2 → ((p2 → (p1 ∧ ((((p3 ∨ p3) ∨ p5) ∨ p3) ∧ (False ∨ p4)))) ∧ (p5 ∨ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183502647201093465561388976531 : ((p4 ∨ (((p2 → (p4 → p5)) ∨ (p3 ∨ (True ∨ p3))) ∨ True)) ∧ (((((p5 ∨ p3) ∧ (True ∧ p4)) → p3) ∧ p1) → ((p1 → False) → p4))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40725369375394888964626927220 : (((((p5 → (p2 → ((p4 → p3) ∨ p3))) ∨ (p2 → (False → ((((p2 ∨ False) ∨ (p1 ∧ p4)) → p5) ∨ (p4 ∧ p1))))) → p1) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43557969044499688492057672692 : (((((((p5 ∨ (p4 ∧ (((p5 ∨ p3) → (p2 ∧ (False ∨ False))) → p2))) ∧ (True → p4)) ∧ (p4 ∨ (p4 → p3))) ∧ p1) → False) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801334872817935864336597636002 : (((p2 → ((p2 → ((((p3 ∧ (p4 ∧ (False → p1))) → False) ∨ (p1 ∨ False)) ∨ p2)) → (p5 ∨ (p2 ∧ (p1 ∨ ((True ∧ False) ∨ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200509769581604471080123553691 : (((True ∨ p3) → ((p4 ∧ (False ∧ False)) ∧ p1)) → (p2 ∨ ((p5 ∧ ((p4 → (p2 ∨ p3)) → ((p4 → (p5 ∨ p1)) ∧ (p1 → p5)))) → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193751461265232985412430566203 : ((p3 ∧ ((True ∨ ((p5 ∨ False) → p5)) ∨ (False → p1))) → ((p1 → ((True → (((False ∧ True) ∨ False) ∧ p4)) → (p2 ∧ (p5 ∧ True)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h8
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- False on the left can always be used.
        apply False.elim h12
      case inr h14 =>
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20
      case inr h22 =>
        -- False on the left can always be used.
        apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h24 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h25 := h3 h24
    -- We need to get the left conjuct of h25 based on <expert-advice>.
    let h26 := h25.left
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- False on the left can always be used.
      apply False.elim h28
    case inr h30 =>
      -- False on the left can always be used.
      apply False.elim h30
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h31 := h1.left
  let h32 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h32
  case inl h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h36 := h3 h35
      -- We need to get the left conjuct of h36 based on <expert-advice>.
      let h37 := h36.left
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Conjunctions on the left can always be decomposed.
        let h39 := h38.left
        let h40 := h38.right
        -- False on the left can always be used.
        apply False.elim h39
      case inr h41 =>
        -- False on the left can always be used.
        apply False.elim h41
    case inr h42 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h43 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h44 := h3 h43
      -- We need to get the left conjuct of h44 based on <expert-advice>.
      let h45 := h44.left
      -- Disjunctions on the left can always be decomposed.
      cases h45
      case inl h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h46.left
        let h48 := h46.right
        -- False on the left can always be used.
        apply False.elim h47
      case inr h49 =>
        -- False on the left can always be used.
        apply False.elim h49
  case inr h50 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h51 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h52 := h3 h51
    -- We need to get the left conjuct of h52 based on <expert-advice>.
    let h53 := h52.left
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- Conjunctions on the left can always be decomposed.
      let h55 := h54.left
      let h56 := h54.right
      -- False on the left can always be used.
      apply False.elim h55
    case inr h57 =>
      -- False on the left can always be used.
      apply False.elim h57
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133585217170674289389650862427 : ((((True ∧ (p1 ∨ ((p3 ∧ ((p2 ∧ (False → (p4 ∨ p3))) ∨ p1)) → (((True ∧ p4) ∨ False) ∨ p4)))) ∨ p2) ∧ True) ∨ (p3 ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39636861198423903358385287952 : (((p3 ∨ (((((((True → (p1 ∧ False)) ∧ (((p3 ∧ p4) ∨ p4) ∧ p1)) → p5) ∨ p4) ∨ p3) → ((True ∨ False) → True)) → p1)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762074711337945194501331601470 : (((p3 ∧ (((p4 → (p2 ∨ ((True → p3) ∨ (p4 ∧ (((p3 ∨ p3) ∨ (p3 ∧ (False → (p3 → p4)))) ∧ p2))))) → p2) ∧ (p2 → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643243316055215888247126359601 : ((((p3 ∧ (((True → p4) ∨ ((True ∨ p4) ∧ p2)) ∨ (((((p3 ∨ p5) ∧ False) ∨ (p5 → (p2 ∧ True))) → p4) ∧ (p2 ∧ p4)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216228264095461573905253569065 : ((p1 → ((p1 → False) ∨ p4)) ∨ (((p2 → (True ∨ (p4 ∧ (p2 ∧ ((p1 ∨ p5) ∨ p3))))) ∨ p1) → (((p5 ∨ p1) ∨ (False → p3)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687014200580902564353765446539 : ((((p4 ∨ (p2 → (((False ∨ p4) → ((False ∨ (p5 ∨ (True ∨ p5))) ∧ p4)) ∧ (p5 → False)))) → ((p4 ∨ (False ∨ (p1 → False))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230568255306401403293615552547 : (((p1 → False) ∧ p2) → (((True → ((True ∧ p4) → ((True → p1) ∧ (p5 ∧ False)))) ∧ (p1 ∨ (((p1 ∧ p2) ∨ (True ∨ p3)) ∧ p4))) → False)) := by
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
    let h6 := h1.left
    let h7 := h1.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h1.left
      let h17 := h1.right
      -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
      have h18 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h16, we can now drive its conclusion.
      let h19 := h16 h18
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h1.left
        let h23 := h1.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h24
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h26 : (True ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h27 := h25 h26
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- We need to get the right conjuct of h28 based on <expert-advice>.
        let h29 := h28.right
        -- False on the left can always be used.
        apply False.elim h29
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h1.left
        let h32 := h1.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h34 := h3 h33
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h35 : (True ∧ p4) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h36 := h34 h35
        -- We need to get the right conjuct of h36 based on <expert-advice>.
        let h37 := h36.right
        -- We need to get the right conjuct of h37 based on <expert-advice>.
        let h38 := h37.right
        -- False on the left can always be used.
        apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208826890326126403706735345934 : ((p3 ∧ ((p1 ∧ True) → (p4 ∧ True))) → (((p2 ∨ ((p4 ∧ ((p3 ∨ False) → ((p5 → (p2 ∨ p1)) ∧ p2))) → (p5 ∨ p2))) ∨ p5) ∨ p3)) := by
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
theorem thm_5_vars_348008722899002353042704344411 : (p3 → ((False ∧ p5) ∨ (((p4 → (False ∧ ((((((p1 → False) → p2) ∧ (p2 ∧ p3)) ∨ True) → p1) ∨ (p1 ∧ p2)))) ∧ p2) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_112280021395209977198827427566 : (((True → (False ∧ (((((True ∨ p1) ∧ p4) ∧ (True → p1)) ∧ False) ∧ ((p4 ∧ ((p2 ∨ p1) ∧ (p2 ∧ p4))) ∧ True)))) ∨ p1) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41027643636094731656165524994 : ((((((p2 → (p5 → (p2 ∧ p3))) → (False ∧ ((p3 ∨ (True ∨ ((False ∧ True) ∧ p4))) ∨ p3))) ∨ (False ∨ p4)) → (p2 ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190673903970489995460717519907 : (((p2 → (((p2 ∨ p2) ∧ (True → False)) → False)) → p2) ∨ ((True → ((p4 ∨ ((p3 ∧ False) → (p4 ∨ p4))) → p4)) ∨ ((p5 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749804562415308078425532977436 : (((True ∧ ((False ∧ (p3 → (p2 ∨ ((((((p3 ∨ p3) ∨ p3) → (((p2 ∨ p2) ∨ True) → False)) ∧ (True → True)) → p4) ∨ p2)))) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77243271737894945510164535710 : (((((p1 ∨ True) ∨ p2) → (((False ∧ p4) ∧ False) ∨ ((True ∧ True) ∨ ((p3 ∧ p4) → (p4 ∨ ((False → p2) ∨ (False → False))))))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ True) ∨ p2) → (((False ∧ p4) ∧ False) ∨ ((True ∧ True) ∨ ((p3 ∧ p4) → (p4 ∨ ((False → p2) ∨ (False → False))))))) := by
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
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
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
    case inr h7 =>
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
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216561826020011022997625716320 : ((((p5 ∧ True) ∧ p4) ∧ p4) → (((p1 ∧ False) ∧ ((((p3 ∨ p3) ∧ (p1 → p1)) → (p2 ∧ p3)) ∧ ((p4 ∧ p2) ∨ p3))) ∨ (False ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152887845778988153890765425836 : ((True ∧ ((((p5 → p3) ∧ (p5 ∨ False)) → False) ∨ ((True ∧ p4) ∨ ((p2 ∨ False) → ((False ∨ False) ∨ p1))))) → (p4 ∨ (False ∨ (p2 ∨ True)))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
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
theorem thm_5_vars_130139303899316983987645154721 : (((((p4 → (p3 → False)) → (False ∧ p1)) ∨ ((((p3 ∨ True) ∨ ((p1 ∨ p3) ∧ p1)) ∨ p1) ∧ True)) ∨ (True → False)) ∧ (False → (p3 ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171529019193439514717467532434 : ((((((True ∧ p2) → ((p4 → p5) → ((False ∨ p3) ∨ True))) → p3) ∨ p3) ∨ p3) ∨ ((p5 ∨ (p3 ∧ (p3 ∨ ((False ∨ p3) → p5)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133700689048162355031133143188 : ((((((p4 ∨ True) → (p4 → ((p2 → ((False ∧ p1) → p1)) ∧ p1))) ∨ p5) ∧ ((p5 ∧ p1) → (True → p4))) ∧ p3) ∨ ((p3 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340895263401505368327643828901 : (p2 → ((((((True ∧ True) ∨ p3) → (p1 ∧ ((False ∨ False) ∨ p4))) ∧ p4) ∨ ((((p2 ∨ False) ∧ False) ∨ (p1 ∧ p4)) → (p1 ∧ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2970695963432151780783998787 : ((p1 ∨ (p1 ∨ p1)) ∨ (p1 → (p2 ∨ (((((p3 ∧ (p2 ∧ p1)) → (p2 ∧ p1)) ∨ p3) ∧ False) ∨ ((p3 ∨ p1) ∨ (True ∧ p4)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342146237920270373142643298655 : (p2 → (((False ∨ ((((((p3 ∨ ((p1 ∧ p3) → p1)) ∨ p2) ∧ p3) ∧ p5) ∨ p1) ∨ (True → p2))) ∨ True) ∨ (p5 → (p2 ∨ (p2 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617197927171230986386979154793 : (((((((False ∧ False) ∧ True) ∧ ((p3 → p2) → False)) ∨ (True ∨ (((p4 ∨ (p1 ∧ (False ∨ p1))) ∧ p5) ∨ ((True ∨ False) ∨ p5)))) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40948568550506818024800406679 : ((((((False → p1) ∧ ((((p4 ∨ ((p1 ∧ p4) ∧ (p2 ∨ p2))) ∧ p5) ∧ (p5 ∨ True)) ∨ True)) ∧ (True → True)) ∨ (False ∨ True)) ∨ p3) ∨ p3) := by
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
theorem thm_5_vars_234075327481651407502117477626 : ((True → (p1 ∧ False)) → (((True ∧ ((p4 → (p5 → p2)) ∧ (False ∧ p4))) ∨ (False ∨ ((p5 ∨ ((p1 ∨ p1) → (p2 → p4))) ∧ p1))) ∧ p4)) := by
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
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60061707820667765996565964603 : (((p2 ∨ p1) → (((p5 ∧ p5) ∨ p2) ∨ ((p1 ∧ ((p5 → p3) ∨ (p4 → (False → (p3 → (p4 ∧ (True ∨ (p1 ∧ True)))))))) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58069974204545309368097331001 : (((False ∧ p4) ∧ ((((False ∨ (p2 → p2)) ∧ (p4 ∨ p5)) ∧ (p3 ∧ (((p5 → p4) ∧ False) ∨ False))) ∧ (((True ∧ False) → p1) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63095460197067549571630659279 : ((p5 ∧ (((p3 ∧ p4) ∧ (((p5 → (p4 → p3)) ∧ True) ∨ (((((p4 → p5) ∨ p4) ∧ True) ∨ (p5 ∧ (p2 → p1))) ∨ p2))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177980148630554108378095246938 : (((p2 ∧ ((((p4 ∨ (p1 ∨ p5)) ∨ (p2 → p2)) ∧ p1) ∧ p4)) ∨ p2) ∨ ((((((p5 → (p2 ∧ False)) ∧ False) ∧ False) → True) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341095592289307713813541808229 : (p2 → ((p2 → (p4 ∧ ((p3 → ((p3 ∨ (False ∧ p5)) → ((p5 ∨ (p3 ∧ ((p5 ∨ (p2 ∧ (False ∧ p4))) ∨ False))) ∨ False))) ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165725805696912456918739177165 : (((p3 ∨ (p5 ∨ (p1 ∧ p2))) ∧ (p3 ∧ ((p3 → p5) ∧ (p4 ∨ (p1 → (True → p4)))))) ∨ ((((p3 ∧ p4) ∨ (p3 ∧ False)) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53539497136062825373846373881 : ((((((p4 ∧ ((False ∧ p3) → False)) → False) → p4) ∧ p3) ∧ (((((p4 ∧ p4) → False) ∧ p5) → (p2 ∧ (p5 → p4))) → (p5 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624155357305385285441803747943 : ((((p2 ∨ (p3 ∨ ((True ∧ (p5 ∧ ((False → (p2 ∧ p2)) ∨ p3))) → (p4 ∧ (p1 ∨ (((p1 ∧ (p5 → True)) ∨ p1) ∨ p5)))))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164839113309808990102358553127 : (((p2 ∧ (((p1 ∨ p5) ∨ (True ∨ (p3 → (p4 ∨ p2)))) → (p5 → (True → False)))) ∨ True) ∨ (True ∨ (p5 ∧ ((p3 → p5) ∨ (p5 → False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



