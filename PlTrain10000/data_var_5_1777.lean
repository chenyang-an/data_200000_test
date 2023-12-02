variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_94640985728564754544189046112 : ((p3 ∧ (((((p4 ∧ (False ∧ True)) ∨ (True ∧ p4)) ∨ p1) ∨ (((False → (True ∨ p1)) ∨ p2) → ((p3 ∨ (p4 ∧ True)) ∨ p3))) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p4 ∧ (False ∧ True)) ∨ (True ∧ p4)) ∨ p1) ∨ (((False → (True ∨ p1)) ∨ p2) → ((p3 ∨ (p4 ∧ True)) ∨ p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118733819594470602388362493242 : ((p5 ∨ (((True ∧ p2) ∨ (((p4 ∧ (True ∧ (True ∨ p3))) ∧ p3) ∨ p4)) ∧ (True → (((p2 → (p3 → True)) ∨ p5) ∧ False)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184812476814558521890143215019 : (((((p5 → True) ∧ p1) ∧ True) → ((p5 ∧ True) ∧ (p5 → True))) ∨ (((p2 → ((((p4 → (p5 ∧ p1)) ∨ p5) → True) → p1)) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10220142948873873393038345195 : (((p2 ∨ (((True → (p1 ∧ p3)) ∧ (p1 ∨ ((((False ∧ (p5 → p3)) → p1) ∨ p2) ∧ p5))) → ((p4 ∧ p1) ∨ (p4 → p1)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55574454024782514532315929694 : (((False ∨ ((p2 ∨ p2) ∧ (p1 ∧ p2))) → ((p3 ∨ p5) ∨ ((p3 ∨ ((p1 → (((p1 ∨ False) ∧ p4) → p1)) ∧ p4)) ∨ (p2 ∧ True)))) ∨ p5) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119110508763157172568365417716 : ((p1 → ((True → p2) ∧ ((True → (p4 ∨ (p2 ∧ ((p5 ∨ (p2 ∨ p1)) ∧ (p3 ∧ (p5 ∨ False)))))) ∨ (True ∨ (p1 ∨ False))))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312288686810948570102639710725 : (p2 ∨ (p2 → ((((p3 → ((False ∧ True) ∨ False)) → (((p5 ∨ (p1 → ((p1 ∨ (p1 ∧ p4)) ∨ (p3 ∨ p4)))) → p4) ∨ p2)) ∨ p3) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134037051472283869216230060569 : (((((p4 ∧ ((p2 → p3) ∨ ((p2 ∨ (p4 → False)) ∧ False))) ∨ (p4 ∧ (p2 ∨ (p4 ∧ (True ∨ True))))) ∨ True) ∨ False) ∨ ((p4 ∨ p1) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166648509787088359134984350416 : ((p1 → ((p4 ∨ (False ∨ ((True ∨ (p4 → p3)) → p4))) → (((False ∨ False) ∨ p2) ∨ p1))) ∨ ((True ∨ False) ∨ (False ∨ (True ∧ (p2 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249115138994959097208695999191 : ((p4 ∨ p2) ∨ ((((False ∧ (False ∧ p4)) → p2) → ((((False → ((False ∨ (p4 ∨ (p1 → False))) → p2)) ∨ p2) → (p5 ∨ True)) ∧ False)) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (False ∧ p4)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112550969278587044288089467188 : (((((p2 ∨ (p5 → False)) ∨ ((((p1 → p5) ∨ False) → (p3 ∧ (True → (True → (p5 ∧ True))))) ∨ (True → p4))) → p4) → p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310850203718042922713132853052 : (p2 ∨ (((p3 → p2) ∨ p5) → ((((p2 → p5) → p2) ∨ (p2 → p2)) ∨ ((p5 ∨ (((False ∧ True) → ((p2 ∧ p5) ∧ True)) ∨ p5)) → True)))) := by
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
theorem thm_5_vars_187084477036733851474371626941 : (((p1 → False) ∧ ((p4 → p2) ∨ (False ∧ ((p4 → p4) ∧ p2)))) → (((((p4 ∨ p3) ∨ p2) ∧ p1) ∨ p1) ∨ ((p4 ∨ (p3 ∧ p4)) → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141264457127981078140135718081 : (((((p2 ∨ p2) → False) ∧ p4) ∧ (p1 ∨ (p3 ∨ ((((p1 → (p2 ∨ (p4 ∧ p2))) → p3) ∧ (p3 ∨ p4)) → p3)))) → ((p5 ∨ p3) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141248814267572026526361993419 : (((p3 ∧ (((p5 ∧ p3) → p2) → False)) → (((False → (p4 ∧ (p4 → p1))) ∨ p2) → (((p1 ∨ p5) → p2) ∧ p5))) → (p1 ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80343570141467679278922553771 : (((((p5 ∨ (((p4 ∧ p3) ∨ (True ∨ (p3 ∨ p3))) ∨ p1)) ∧ ((p1 ∧ p1) ∨ p4)) → (((p2 ∧ True) ∨ True) ∧ True)) → (p2 ∧ False)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (((p4 ∧ p3) ∨ (True ∨ (p3 ∨ p3))) ∨ p1)) ∧ ((p1 ∧ p1) ∨ p4)) → (((p2 ∧ True) ∨ True) ∧ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h16.left
            let h18 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h5
            case inl h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h22.left
              let h24 := h22.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Disjunctions on the left can always be decomposed.
              cases h5
              case inl h28 =>
                -- Conjunctions on the left can always be decomposed.
                let h29 := h28.left
                let h30 := h28.right
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
              cases h5
              case inl h33 =>
                -- Conjunctions on the left can always be decomposed.
                let h34 := h33.left
                let h35 := h33.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h36 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h41 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h42 := h1 h2
  -- We need to get the right conjuct of h42 based on <expert-advice>.
  let h43 := h42.right
  -- False on the left can always be used.
  apply False.elim h43



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157247728237260231108555199049 : ((((p2 ∧ (p3 → ((p4 ∨ p5) ∧ p1))) ∧ ((p3 ∧ (p1 ∧ (False ∧ p5))) → (p1 ∧ p3))) → p1) ∨ (False ∨ (False → ((p2 ∨ True) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40891497588877684504629691458 : ((((((p2 ∧ p5) ∧ (p1 ∧ p5)) ∧ (((True ∧ p4) ∨ (((True ∧ p4) → ((True → p4) ∨ p5)) ∧ True)) ∧ p3)) ∧ (False ∨ p1)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147071199649836753834006999122 : (((((p3 ∧ False) ∨ (p2 ∨ (False → p3))) ∧ (p4 → (((p3 ∨ (p2 ∨ p2)) ∧ (p5 ∨ p4)) → False))) ∧ False) ∨ (True ∨ (p2 → (p3 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135825690630637243521834383779 : (((((p5 ∧ p5) ∧ ((p1 → p1) → (p2 ∧ p5))) ∨ (p3 → p2)) ∧ (False ∧ (p4 ∧ (((p2 → p4) ∧ True) ∨ p2)))) ∨ ((p2 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216767826512930797660181715407 : ((((p5 → False) → p1) ∧ p1) → ((p2 ∧ ((p2 ∧ ((p2 ∨ p5) ∨ p2)) ∧ (p3 ∧ (p5 ∧ p5)))) → ((p4 ∨ p4) → ((p2 ∧ False) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h8.left
        let h14 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Conjunctions on the left can always be decomposed.
        let h17 := h1.left
        let h18 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h8.left
        let h21 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h1.left
        let h25 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h8.left
      let h28 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h1.left
      let h32 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26
  case inr h33 =>
    -- Conjunctions on the left can always be decomposed.
    let h34 := h2.left
    let h35 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h36 := h35.left
    let h37 := h35.right
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h37.left
        let h43 := h37.right
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h1.left
        let h47 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h37.left
        let h50 := h37.right
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Conjunctions on the left can always be decomposed.
        let h53 := h1.left
        let h54 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h38
    case inr h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h37.left
      let h57 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h58 := h57.left
      let h59 := h57.right
      -- Conjunctions on the left can always be decomposed.
      let h60 := h1.left
      let h61 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h55



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725994079103953521295519690423 : (((((p4 → p4) ∧ p4) ∨ ((((p3 → (p3 ∨ p3)) → p4) ∨ (((p1 → False) ∧ p4) → (((p3 ∨ p5) → p5) ∧ p4))) ∨ (True ∧ True))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152114080025943428913145836727 : ((((True ∧ (((p1 → p4) → True) → False)) ∨ False) ∧ (((p1 ∨ p2) → ((p2 ∧ True) ∧ (p2 ∧ p5))) ∧ p5)) → (((p2 → False) ∨ p2) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200400411203432256105026933223 : (((p3 ∧ True) ∨ (((p4 → p2) ∨ True) ∧ True)) → ((p2 ∨ (p5 ∧ ((((False ∧ True) ∨ (False → p3)) ∧ p5) → (p3 ∨ p3)))) ∨ (p2 → True))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611798072371511139964115646219 : (((((p1 → (p4 → ((p2 ∨ p5) ∧ (((p5 ∧ p5) ∧ p5) → (p3 ∧ ((((p3 ∧ (p1 ∨ True)) → False) → p3) ∨ p4)))))) → p1) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_256779675961987292933210842198 : ((p1 ∨ p2) → ((True → (((p5 → (p1 → (p3 → p1))) ∧ (p4 ∨ (p4 ∨ p1))) ∧ (p3 ∨ p4))) ∨ ((p5 → False) ∨ ((p1 ∧ p3) ∨ True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136402405453313583389413677260 : (((p5 ∨ (p2 ∧ (False ∧ p3))) ∨ ((p4 ∧ (p4 → (p4 ∨ (p4 ∨ (p5 ∨ ((p1 ∨ (p4 → False)) → p2)))))) ∨ True)) ∨ (p1 ∧ (p4 ∧ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178501357938950823911601707315 : (((p2 ∨ ((p5 → (p4 → (p3 → p3))) → p3)) ∨ (p2 → (False → p2))) ∨ ((((((p4 ∨ p1) ∧ p3) → False) ∧ (p1 → p2)) → False) ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750082420792973208055524714669 : (((True ∧ ((p1 ∧ ((p2 → (p5 ∧ False)) ∧ ((p1 → (p1 ∨ (((p1 ∧ p3) ∧ p2) → p2))) → (p4 ∨ (p5 ∨ (p5 ∨ False)))))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221460530881777039625749504892 : (((False → p4) ∨ p4) ∧ (((False ∨ (p1 ∨ p3)) ∧ ((True → p2) → ((p4 ∧ (True ∧ (p4 ∧ p5))) ∨ (p1 → True)))) ∨ (False ∨ (p5 ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303011118495975823010063916629 : (False ∨ (p1 → ((p3 ∨ ((p5 ∧ p2) ∨ p3)) ∨ ((((((p5 → False) ∧ p2) → (False ∨ (False ∧ p5))) → (True ∧ True)) ∨ p4) ∧ (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254272956074831026832637770002 : ((p2 ∧ p3) → ((p1 ∨ ((((p4 ∧ p2) ∧ ((((p5 ∨ p1) → (p1 ∨ ((False → p4) ∨ p1))) ∧ p3) ∧ p3)) ∨ (False ∨ False)) ∧ p5)) ∨ True)) := by
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
theorem thm_5_vars_791889410681129752867018241280 : (((True → (((((p3 ∧ ((p3 → ((p5 ∧ False) ∧ (p4 ∧ p1))) ∧ p2)) ∨ (p5 ∧ ((p2 → p2) → p3))) → p4) ∧ False) ∨ (p4 → p4))) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215017522817454796132132840380 : (((False ∨ p5) → (p1 ∨ False)) ∨ (((p2 ∨ ((p1 → (p1 → p2)) → p3)) ∨ ((((False ∧ p1) ∨ p4) ∨ p2) ∧ (True → (p4 ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766515380295537804788951495807 : (((p4 ∧ (p3 ∧ ((p4 ∧ (p3 ∨ (((p4 ∧ (True → p3)) ∨ p1) ∧ (False ∧ (False ∧ (((False → (True → True)) ∧ p3) → p5)))))) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199921929391609664613623932347 : ((((False ∧ True) ∨ (p4 ∨ p3)) ∨ (p4 ∨ p1)) → ((((p3 ∨ False) ∨ p3) → p4) → (p2 → ((p2 ∧ p1) → (True ∧ ((p5 ∧ p4) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47016463932539788951157580761 : ((((p5 ∧ (p3 ∧ ((((False ∧ p1) → p1) → p4) → (p2 ∧ (((p3 ∨ (p3 → (False → p3))) ∨ p3) → p1))))) → False) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41266303461353275425893188249 : ((((p4 ∧ (p4 ∧ (False ∨ (True ∧ (False ∨ (((p5 ∧ p3) ∨ (False → (p5 ∨ p2))) → p1)))))) ∨ (p2 → (False → (True ∨ True)))) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151996513961762649675811385728 : ((((True ∧ ((False ∨ p3) ∨ (p5 ∧ p2))) ∧ ((p2 ∧ True) ∨ p2)) → ((True ∨ (p1 ∧ p5)) ∨ (p2 ∧ p1))) → (((p3 ∨ True) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691243458800024813588893728650 : (((((p1 ∨ ((p2 ∧ p2) ∨ p3)) ∧ ((((p4 → p5) ∨ False) ∧ p3) ∨ (True → False))) → ((p3 ∧ p2) ∨ ((False → p4) ∨ (p4 ∨ p4)))) ∨ p4) ∧ True) := by
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
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h20
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h25 := h23 h24
        -- False on the left can always be used.
        apply False.elim h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- False on the left can always be used.
          apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
        have h34 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h33, we can now drive its conclusion.
        let h35 := h33 h34
        -- False on the left can always be used.
        apply False.elim h35
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134500275975816473147060147601 : (((((((False → p1) ∨ (p5 ∨ p2)) → (True ∧ (p1 → p4))) → (((p4 → False) ∧ (p1 → p5)) ∨ p5)) ∨ True) → p1) ∨ ((False ∧ p4) → p4)) := by
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
theorem thm_5_vars_118443503324663542290548335745 : ((p3 ∨ (((((((p3 → (p3 ∨ p5)) ∨ (p4 ∧ (p1 → (p4 ∨ (p5 ∧ (False → True)))))) → p2) ∨ p4) → False) ∨ p5) ∧ False)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191121347069361012672193594401 : (((p5 ∨ (p4 ∨ p2)) ∧ ((p4 → (p2 ∧ p4)) ∨ p1)) ∨ (((True ∨ ((p2 → False) ∨ p3)) ∨ ((False → p1) → (p1 ∧ p1))) ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136082314337754308526838204506 : (((p4 ∨ ((((False → p3) → True) → p2) ∧ False)) ∧ ((((p3 → p5) ∧ p2) → (p3 ∨ p5)) ∧ (p5 ∧ (True → True)))) ∨ (True ∨ (p3 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587885273031179547088017692927 : ((((((((p2 ∧ p2) ∨ p1) ∧ ((False → p3) ∨ (((p2 → ((True ∨ p3) ∧ p3)) ∨ p5) → (p1 → p5)))) → (p2 ∧ p5)) ∨ p1) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735584268739757391319634158008 : ((((p5 ∨ True) ∧ (p2 → ((p1 → ((((p4 ∨ p4) ∨ ((True → p4) ∨ p5)) ∧ p5) ∧ p4)) ∨ ((False ∧ (True ∨ p3)) → (True ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656837613622407690001637427326 : (((((((p1 ∧ p5) ∨ p3) → True) ∧ ((True ∧ (p3 ∧ (((False ∨ ((p4 ∨ (p1 → p5)) ∨ p3)) ∨ p1) ∨ False))) → p5)) ∨ (p3 → True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_322632851225333296507705188929 : (p5 ∨ ((((((p2 → (True ∧ p2)) → (p3 ∧ (((p5 ∨ (p5 → (p3 ∨ p4))) ∨ p4) ∨ p4))) → (p2 ∧ p3)) ∧ (p2 → p4)) ∧ p3) → p4)) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p2 → (True ∧ p2)) → (p3 ∧ (((p5 ∨ (p5 → (p3 ∨ p4))) ∨ p4) ∨ p4))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h6
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330349282218842260885975749551 : (True → (p1 ∨ (p5 → (p3 → ((p3 → (((False ∨ (p3 → False)) ∨ (p2 ∨ (p4 → False))) ∧ ((False ∧ p1) ∨ (p3 ∨ p3)))) ∨ (p1 → True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52855027889552171576405869533 : ((((p1 → p2) → ((p2 ∧ ((p5 ∨ True) → False)) ∧ (p3 ∧ (p1 → p2)))) → (((p3 → (p3 ∨ ((False → p5) → True))) → p4) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713200558751954164275298769267 : ((((p1 ∨ (p3 → (p1 ∧ (p5 ∧ p3)))) ∨ ((p1 ∧ p5) → ((p3 → False) ∨ ((p3 ∧ ((False ∧ p4) ∧ False)) ∨ ((p1 → p4) → True))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114110399110862729770789451939 : (((p1 ∨ ((p5 ∧ ((((((True → (False → False)) ∨ p3) ∧ (p3 ∧ p2)) ∨ p2) ∧ p1) ∨ True)) ∧ p2)) ∨ ((False ∨ p2) ∨ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213542431876541476379799402781 : ((((p2 ∧ False) ∧ p3) ∨ p3) ∨ (p1 → ((((p4 → True) ∧ ((p4 ∨ p4) ∨ (True → p2))) → ((p3 → (p5 ∧ p2)) ∨ (p4 → p1))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53294334699612280381104336184 : (((p1 ∨ (((False ∧ (False → p1)) ∨ p2) ∨ (True ∧ (False ∨ False)))) ∨ (False ∨ ((p4 → ((p5 → p4) ∧ (False → (False → p3)))) ∨ p4))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135607245857597448832167773633 : ((((False → p3) → (p2 ∧ (p2 ∧ (p3 ∨ (p2 ∧ ((p2 ∧ (p5 ∧ p5)) ∨ p5)))))) ∨ (((p2 → p3) ∧ p4) ∧ True)) ∨ (True ∨ (p2 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303029813763249457612541093763 : (False ∨ (p1 → (p5 ∨ ((((p1 → (p5 → ((p1 ∧ ((p2 → p2) ∧ p5)) ∧ p1))) → ((p3 ∨ p2) ∨ p3)) → (p5 → (p1 → False))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62960035341126605694748585843 : ((p4 ∧ (False ∨ ((p2 ∨ ((((p4 → p5) ∧ ((p4 ∧ (p3 ∨ False)) ∨ p3)) ∧ p1) ∨ True)) ∧ ((p2 ∨ p5) ∨ (False ∧ (True → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147661847884916809953097702305 : (((((p1 → (p4 ∧ (p5 ∧ (True ∧ True)))) ∧ ((False ∨ p4) → (False → (True ∧ p2)))) ∨ (True ∨ p1)) → p5) ∨ (p2 → ((p1 ∧ p5) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636669888904720553470770190141 : (((((((p1 → ((p1 → (True → False)) ∨ p1)) → p5) ∧ ((p5 ∨ p2) ∨ p3)) ∨ (p4 ∨ ((p1 ∨ p5) ∧ ((p2 → p4) ∧ p5)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261316110690932107688133888333 : ((p5 → False) → (((((p2 ∨ False) ∨ p5) ∨ p1) ∨ (p5 → ((p4 ∧ (p3 ∧ (True ∧ (p5 → p2)))) ∧ ((p3 ∨ p2) ∧ (False ∨ False))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h10
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114202501841545347524712578221 : (((((p4 ∧ p1) ∨ ((p1 ∧ p5) ∧ p4)) → (p3 ∧ (((False ∧ p1) ∨ (False ∨ (p5 ∧ p5))) → p4))) → (p1 ∨ (False ∨ False))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763227149832242569233825850323 : (((p3 ∧ ((False ∧ p3) ∨ ((p2 → ((p2 ∧ (p4 ∨ (p5 ∨ (((p5 → ((p4 → p3) ∧ (p4 → p1))) ∧ p1) → False)))) ∨ False)) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714751198376572008097236898793 : ((((True ∧ (p2 → (p1 ∨ (p4 ∨ p3)))) → (((((p2 ∧ (False ∧ (p3 ∧ False))) ∨ p2) → p3) ∧ (p2 ∧ (False ∨ p5))) ∧ (p3 ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350964190553007213795689385659 : (p4 → (((p4 ∨ ((p2 → p1) → ((p1 ∨ True) ∨ p2))) ∧ ((p5 ∧ (p1 ∨ (p1 ∧ (p1 ∧ ((p5 ∨ p2) → p3))))) → False)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265693564874328837119467977089 : (True ∧ (p3 ∨ ((((p2 ∧ (False ∧ (((p2 ∧ (p1 → ((False ∧ p4) ∨ (((p2 ∨ p5) → False) ∨ p1)))) ∨ p4) ∧ p5))) ∧ False) ∨ p2) ∨ True))) := by
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
theorem thm_5_vars_67896622186258280029379123242 : ((p2 → ((p1 ∨ (((p4 ∧ (p3 ∨ (True → p3))) ∧ ((p5 → (p3 ∨ p5)) ∧ p3)) ∨ p1)) ∨ ((True ∧ False) ∨ (p2 ∨ (p5 ∨ True))))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4292343544883803931045668702 : (True → (((p2 → p4) → (p3 ∧ ((p4 → p1) ∨ p1))) → ((p4 ∧ p3) → ((((p2 ∨ p2) ∧ p4) ∧ False) ∨ (p3 → (p2 ∨ p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197802933860350709537714502679 : ((((p1 ∨ p1) ∨ p3) ∨ (p4 ∧ (True ∧ False))) ∨ ((((p5 ∧ ((((p5 ∨ ((False → p3) → p3)) → p2) ∨ False) → p4)) ∨ p3) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231137859517852119751151612786 : (((p1 ∨ p3) ∨ p4) → (((((p3 → (p4 → False)) ∧ ((p3 ∧ p4) ∧ ((True → p2) → (p5 → (False ∨ True))))) → False) ∨ p5) ∨ (p1 ∨ False))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h13 := h6 h12
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h14 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h15 := h13 h14
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h24 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h25 := h18 h24
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205515686675692296107191288987 : (((p5 ∧ p2) ∧ (p1 ∧ (False ∧ p5))) ∨ (((p3 ∨ (p4 ∨ ((p4 ∨ ((p4 ∨ ((p5 → p4) → p2)) ∨ p1)) ∧ p3))) → (p5 ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226030095864274555626023603111 : (((p4 ∧ p5) ∨ p1) ∨ (p2 ∨ ((((True ∨ (((True ∧ (p3 ∧ (False ∨ True))) ∨ p4) → False)) ∧ (p3 ∧ True)) ∨ (False → (p4 → p1))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151314249513264533881354504895 : (((p4 ∨ ((((p2 ∧ ((p3 ∧ ((p2 → p3) ∨ p3)) ∨ False)) ∨ (p1 ∧ p2)) → (p3 ∨ p1)) ∨ p3)) → p2) → ((p3 → (p1 ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149594509063040700902963483748 : ((p3 ∧ ((((p4 ∨ ((((True ∨ True) ∨ (p4 ∨ p1)) → (p1 ∧ p1)) ∨ p2)) ∧ p4) → p1) → (p2 ∧ p5))) ∨ (p4 → (p4 ∧ (True ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67494831043525962640364088547 : ((p1 → (((p5 ∧ ((True ∧ p5) → (p2 ∨ (p3 ∨ p3)))) ∨ p2) ∧ ((p4 ∧ p3) ∨ (((p5 ∨ (True ∨ p5)) ∧ p4) ∨ (p5 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169385803536585247011551397744 : ((((((p4 → ((((False ∧ p1) ∧ p2) ∧ True) ∧ p3)) ∨ p2) → False) ∨ p1) ∨ True) ∧ (True ∨ (((p5 → ((p1 → False) ∧ p2)) ∨ p4) → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186525892641952682429522226963 : ((((p1 ∨ ((p4 ∧ (True → p2)) ∨ p2)) ∨ p5) ∨ (p5 → p2)) → (p5 → ((False ∨ (((p1 ∧ p5) ∧ p5) ∨ ((False ∨ p1) ∨ True))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
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
        case inr h10 =>
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
    case inr h11 =>
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
  case inr h12 =>
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
theorem thm_5_vars_317801694622331791129129471018 : (p4 ∨ (((((p2 ∨ (p2 → (p2 → p5))) → True) ∨ p4) → ((True ∨ False) → ((p2 ∨ p4) → (((p2 ∧ True) ∨ p1) ∨ (p5 ∨ p4))))) ∨ p5)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h4
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53305333361439009811023619335 : (((p5 ∨ ((((p5 ∨ ((p4 → False) ∧ p4)) ∨ p4) ∨ True) ∨ p2)) ∨ ((True → ((False ∨ ((False → p5) ∨ True)) → (p3 ∧ p3))) → p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248598636220922830691528784187 : ((p3 ∨ False) ∨ (True ∧ (p1 → (p3 ∨ (((False ∧ p3) ∨ (p5 → ((True → ((False → p5) → p5)) → ((p5 ∨ (True → p1)) ∧ p1)))) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738946787799521470520452372789 : ((((p3 ∧ p1) ∨ ((((p1 ∧ (p2 ∨ (True → (p4 ∨ (p2 → (p2 → p5)))))) ∨ (True ∨ True)) ∧ (False → False)) ∨ (True → (p5 ∧ False)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809745757542338378899000824121 : (((p5 → ((((p3 ∨ (p4 → (((True ∨ (p4 ∧ p2)) ∨ p2) ∨ p4))) → (p2 ∨ (((p5 ∨ p5) ∧ True) → p1))) ∧ p2) ∨ (p4 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157291844675148637359795364544 : ((((p2 → True) ∨ (p1 ∨ (((True → (p2 ∧ (p4 ∧ p5))) → p2) ∨ ((False → p4) ∧ True)))) → p3) ∨ (p1 → (p4 → (p1 ∧ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205555912147067415924995232803 : (((p4 ∨ p5) ∧ (p2 ∨ (p3 ∨ p1))) ∨ ((p5 → ((False → p4) ∨ p2)) ∨ ((((p4 ∨ (((p2 ∨ True) ∧ p5) ∧ False)) → True) → False) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700117487174241934633635257129 : (((((p4 → (p2 → p3)) → ((False ∧ p5) → (p3 → (p3 ∧ p2)))) → (((p4 ∨ (p5 ∧ p1)) → (p4 → (True → p1))) ∨ (True ∧ True))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_59048808905104587861562639117 : (((p4 ∧ p3) ∨ (((p5 ∨ ((p1 ∨ True) → (True ∨ (p4 → p4)))) ∧ (p2 → p2)) → (p4 ∧ ((p1 ∧ p2) ∨ (False → (p4 → p1)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312779408864539393931440160588 : (p3 ∨ (((p1 ∨ ((p3 ∨ False) ∧ p2)) → ((((True ∧ True) ∧ ((False ∨ p4) ∧ (p4 → (p4 → ((p3 → p5) ∧ p3))))) → p2) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46557148407493208441053061916 : ((((p2 ∨ False) → ((True → (p2 ∧ (True → p5))) ∨ ((p1 → (p5 → ((p5 ∨ True) → False))) ∨ ((p5 ∧ True) ∧ p1)))) ∧ (p4 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607037498068210981341772729912 : ((((((p3 ∧ ((((False → p1) ∧ False) ∧ (True ∨ (p2 → p3))) ∧ p4)) ∨ ((True ∨ p5) ∧ ((p1 → p3) ∨ (False → True)))) ∧ True) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138032942194577896180121148595 : ((True → (((True → ((p4 ∧ p1) ∨ (False → (((p5 ∧ (False ∧ p2)) ∧ p4) → p5)))) ∨ True) → ((p2 ∨ p3) ∧ p5))) ∨ (False → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313099795406590478620130925422 : (p3 ∨ (((p2 ∨ (((((p3 ∨ (p3 ∨ p4)) → True) ∧ p2) ∨ ((True ∨ (p2 ∨ (True → (p1 ∧ p1)))) ∧ p2)) ∨ p2)) → (p5 ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342810716653150964731280062743 : (p2 → (((((p1 ∨ p1) ∧ True) ∧ p4) ∨ True) ∧ ((p1 → ((((((p2 → p2) ∧ p3) ∨ p2) ∧ True) ∨ p2) ∨ (p5 → False))) ∧ (p3 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143037129968939058519243107562 : ((False → ((p2 ∧ (((p1 ∧ (p4 → p2)) ∨ True) ∨ (p1 ∨ (((p5 ∧ ((p1 ∧ p3) → p4)) ∨ p4) → p1)))) ∧ p2)) → (p2 → (p3 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44093540422892955488611986806 : ((((p3 ∨ ((p1 ∧ p5) ∨ (True → ((((((True ∨ (True ∧ p4)) → False) → p5) → False) ∧ True) ∧ False)))) ∧ ((p3 ∧ p4) → False)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68086604786615184838617408881 : ((p2 → (p4 ∨ (p1 → ((((((p1 ∧ (p1 → p4)) → p5) ∧ p2) → False) ∨ p3) ∧ (((p4 → ((p3 ∨ p4) → p3)) → p1) → p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47385721384327657036337781250 : ((((p4 ∨ True) → (p4 ∨ ((((p3 ∨ ((p5 ∨ True) ∨ True)) → p5) ∧ (p1 ∨ ((p3 ∧ p5) ∧ p4))) ∧ (True ∧ p5)))) ∨ (True ∨ p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310028648070702969907849003390 : (p2 ∨ ((((True → ((p3 → p2) ∨ (p1 → False))) → (p4 ∧ True)) → (p2 ∧ (p5 ∧ False))) ∨ (False → ((p2 ∧ p3) → (p2 ∧ (True ∨ p1)))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42363294653309036004914871266 : (((p3 ∧ (p4 ∨ (True ∧ (((p1 ∨ (p3 → (((p1 ∧ p3) ∧ p1) ∨ ((p2 ∧ (True → p3)) ∨ (p2 → p4))))) ∧ True) ∧ p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711021084900838399341695575639 : (((((p3 ∨ p4) → (p4 → (True ∧ p3))) ∧ (p2 ∨ (p3 ∨ ((p3 → (((True ∧ False) ∨ False) ∧ ((p4 ∨ (p2 ∧ p1)) → p1))) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300865798792524926046733314045 : (False ∨ (((False ∧ (False ∨ ((True ∧ ((p5 → p3) ∧ p5)) ∧ (p1 → False)))) ∧ p4) ∨ (((p3 ∧ p2) ∨ p4) ∨ ((p4 ∧ True) → (p4 ∧ True))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596147659825742870954829690354 : ((((((((p1 ∨ p5) → p3) ∧ (p5 ∧ p3)) ∧ p1) ∧ ((p2 ∨ p4) ∧ ((p3 ∧ (p2 ∧ False)) ∧ ((False ∧ p3) → (p2 → p5))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



