variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168813538564437843827954692323 : ((p2 ∨ ((p3 ∨ p1) ∧ (p3 → ((p3 ∧ False) ∨ ((p2 ∨ p2) ∧ (p4 → (p1 → p1))))))) → ((((p4 → p1) ∨ p5) ∨ True) ∨ (p3 → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347222508882576827646191249666 : (p3 → (((False → (p3 → ((p5 ∨ p1) → (p1 ∧ p4)))) ∧ (p3 → p5)) → ((p3 → (p2 ∧ ((p1 ∨ p2) ∧ (p3 ∧ p5)))) ∨ (p4 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203727604010429345900032969060 : ((p4 ∨ (p5 → (p4 ∨ (True ∧ p5)))) ∧ ((p1 ∨ p1) → (((p3 ∧ p4) ∨ (((False ∧ p4) ∧ p5) ∨ ((p1 ∨ p3) ∨ (p5 → True)))) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_387728244328357361537487613969 : (((((((p1 ∧ False) ∨ ((p2 ∧ ((p3 ∧ p3) → False)) ∨ (False ∨ (False → p5)))) → ((True ∨ False) ∧ p5)) → (p3 ∧ (p2 ∧ True))) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_41182600445241631484398593093 : ((((((True → p4) ∨ (((p4 ∨ ((p5 ∧ p4) ∨ False)) ∨ (p3 → p3)) → (p1 ∧ p5))) → (True ∧ True)) → ((p2 ∧ p4) ∧ p5)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9946801079394923099154682541 : (((p2 ∧ ((p4 → (p2 ∨ (((p4 ∧ (True ∨ (p3 ∨ p1))) ∧ p4) → p5))) → ((((p1 ∧ p3) ∨ p2) → (p5 ∧ True)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780302160652766334011168124259 : (((p2 ∨ ((((False → (False ∧ (p4 ∨ ((p4 → p4) → (p5 ∧ False))))) ∧ (p4 ∧ (p3 ∧ False))) ∧ p5) ∨ ((p1 ∨ (p4 → p2)) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65050488164172749960209266114 : ((p2 ∨ (p1 ∧ ((((p1 → ((p3 ∨ (p1 ∨ (((p1 → p4) ∧ (p2 ∨ ((p5 ∧ False) → True))) → p2))) → p4)) ∧ p1) → p1) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936958703519775353183791997693 : ((((((True → False) ∨ (False → p2)) → False) ∧ ((p2 ∨ (p4 → (p2 → ((p3 → (p5 → (p4 → p2))) ∨ (p4 ∧ p2))))) ∧ (True ∨ p5))) → p2) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : ((True → False) ∨ (False → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- False on the left can always be used.
        apply False.elim h12
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : ((True → False) ∨ (False → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149077069018411918933941760239 : ((((p3 ∧ p3) → p5) → ((p4 ∨ p4) → (((p5 ∨ p5) ∧ (p1 ∨ p3)) → (p5 ∧ (p4 ∧ (p4 ∨ False)))))) ∨ (p5 ∨ (p2 → (p1 → p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h8 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h18 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h19 =>
        -- One of the premise coincides with the conclusion.
        exact h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h20 := h3.left
  let h21 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h31 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h35
  -- Conjunctions on the left can always be decomposed.
  let h36 := h3.left
  let h37 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h36
  case inl h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h40 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h40
      case inr h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h41
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h43 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h44
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h46 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h47 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h47
      case inr h48 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h48
    case inr h49 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h50 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h50
      case inr h51 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56355003208457500360792234571 : ((((p3 ∧ (p4 → p4)) ∨ p3) → ((((p4 → p5) → p4) ∧ ((p3 ∧ p3) ∨ ((((p2 ∧ p4) ∧ (p4 → p4)) ∧ p1) ∨ p3))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115320193613851190704244225091 : (((((False ∧ True) ∧ False) → ((True → (p4 ∧ False)) ∨ False)) → ((((p2 → p5) → (p3 → p1)) → (p1 ∨ (p5 → p4))) → False)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326942357165422870229300376196 : (True → ((((True ∨ ((((((p4 ∨ False) → (True ∨ p4)) → p3) ∧ p5) ∨ True) → p3)) → (False ∨ (True → (p5 ∧ False)))) ∧ (p2 → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113472158953919263793981995213 : ((((p4 → (p2 ∨ ((((p2 → False) ∨ (False ∨ (True ∨ p3))) ∧ (p5 → p3)) → ((p1 ∧ p3) ∧ p2)))) → p3) ∨ (False → True)) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105137511865547663942201035309 : (((((p5 ∧ (p1 → (p4 ∧ p1))) ∨ (p4 ∧ p2)) ∧ (False ∧ (((p2 → p1) ∨ p3) ∨ (True ∧ p1)))) ∨ (p3 → (p3 ∧ True))) ∧ (True ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_928494551578744631338066440756 : ((((p3 ∨ (p1 ∨ ((p3 ∨ ((p3 ∨ p3) ∨ True)) ∧ p2))) ∧ ((False → (p3 ∨ p5)) → (((((False ∨ True) ∧ p1) ∨ p1) ∧ False) ∨ p4))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p3 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h11.left
        let h13 := h11.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h17 =>
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (False → (p3 ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h22 := h3 h20
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- False on the left can always be used.
            apply False.elim h25
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h25
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h36 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h37 : (False → (p3 ∨ p5)) := by
          -- Implications on the right can always be decomposed.
          intro h38
          -- False on the left can always be used.
          apply False.elim h38
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h39 := h3 h37
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Conjunctions on the left can always be decomposed.
          let h41 := h40.left
          let h42 := h40.right
          -- Disjunctions on the left can always be decomposed.
          cases h41
          case inl h43 =>
            -- Conjunctions on the left can always be decomposed.
            let h44 := h43.left
            let h45 := h43.right
            -- Disjunctions on the left can always be decomposed.
            cases h44
            case inl h46 =>
              -- False on the left can always be used.
              apply False.elim h46
            case inr h47 =>
              -- False on the left can always be used.
              apply False.elim h42
          case inr h48 =>
            -- False on the left can always be used.
            apply False.elim h42
        case inr h49 =>
          -- One of the premise coincides with the conclusion.
          exact h49
      case inr h50 =>
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h53 : (False → (p3 ∨ p5)) := by
              -- Implications on the right can always be decomposed.
              intro h54
              -- False on the left can always be used.
              apply False.elim h54
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h55 := h3 h53
            -- Disjunctions on the left can always be decomposed.
            cases h55
            case inl h56 =>
              -- Conjunctions on the left can always be decomposed.
              let h57 := h56.left
              let h58 := h56.right
              -- Disjunctions on the left can always be decomposed.
              cases h57
              case inl h59 =>
                -- Conjunctions on the left can always be decomposed.
                let h60 := h59.left
                let h61 := h59.right
                -- Disjunctions on the left can always be decomposed.
                cases h60
                case inl h62 =>
                  -- False on the left can always be used.
                  apply False.elim h62
                case inr h63 =>
                  -- False on the left can always be used.
                  apply False.elim h58
              case inr h64 =>
                -- False on the left can always be used.
                apply False.elim h58
            case inr h65 =>
              -- One of the premise coincides with the conclusion.
              exact h65
          case inr h66 =>
            -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
            have h67 : (False → (p3 ∨ p5)) := by
              -- Implications on the right can always be decomposed.
              intro h68
              -- False on the left can always be used.
              apply False.elim h68
            -- We have shown the premise of h3, we can now drive its conclusion.
            let h69 := h3 h67
            -- Disjunctions on the left can always be decomposed.
            cases h69
            case inl h70 =>
              -- Conjunctions on the left can always be decomposed.
              let h71 := h70.left
              let h72 := h70.right
              -- Disjunctions on the left can always be decomposed.
              cases h71
              case inl h73 =>
                -- Conjunctions on the left can always be decomposed.
                let h74 := h73.left
                let h75 := h73.right
                -- Disjunctions on the left can always be decomposed.
                cases h74
                case inl h76 =>
                  -- False on the left can always be used.
                  apply False.elim h76
                case inr h77 =>
                  -- False on the left can always be used.
                  apply False.elim h72
              case inr h78 =>
                -- False on the left can always be used.
                apply False.elim h72
            case inr h79 =>
              -- One of the premise coincides with the conclusion.
              exact h79
        case inr h80 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h81 : (False → (p3 ∨ p5)) := by
            -- Implications on the right can always be decomposed.
            intro h82
            -- False on the left can always be used.
            apply False.elim h82
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h83 := h3 h81
          -- Disjunctions on the left can always be decomposed.
          cases h83
          case inl h84 =>
            -- Conjunctions on the left can always be decomposed.
            let h85 := h84.left
            let h86 := h84.right
            -- Disjunctions on the left can always be decomposed.
            cases h85
            case inl h87 =>
              -- Conjunctions on the left can always be decomposed.
              let h88 := h87.left
              let h89 := h87.right
              -- Disjunctions on the left can always be decomposed.
              cases h88
              case inl h90 =>
                -- False on the left can always be used.
                apply False.elim h90
              case inr h91 =>
                -- False on the left can always be used.
                apply False.elim h86
            case inr h92 =>
              -- False on the left can always be used.
              apply False.elim h86
          case inr h93 =>
            -- One of the premise coincides with the conclusion.
            exact h93
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703289389266742298625458942711 : ((((p4 ∧ ((((p2 ∨ p1) ∨ (p2 ∧ p4)) → p4) → p5)) ∨ (((True ∧ p3) → p1) → ((True → ((p2 → p2) → p2)) ∨ (True ∨ False)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_468216384252387858173528398726 : ((((p4 ∨ ((((p3 ∨ p4) → p1) ∨ (((False ∨ p4) → p3) → p1)) → False)) ∨ (((((p3 → False) ∨ p5) ∨ p4) ∧ p3) → (True → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696323978177380230155130301537 : ((((p2 → ((((False → p2) ∧ (p1 ∧ p1)) ∧ p4) ∧ ((p4 → True) → p2))) → (False ∧ (((p4 ∨ p5) → p5) ∨ ((p4 ∨ p5) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48686234680984754971497857442 : (((((p2 ∧ (p2 ∧ (p5 → p3))) → (p2 ∧ p1)) ∧ ((((p3 → (p2 ∧ True)) ∧ p1) ∧ (p3 → p5)) ∨ p1)) ∧ ((p4 ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54141999184561294879424432405 : (((True → (((((p1 → p5) ∧ p3) ∨ p5) → False) ∨ True)) → (((((p2 ∨ p1) → (p5 ∨ (True ∧ (False ∧ p1)))) → p5) → p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142370245314016610772958919272 : ((p3 ∧ (p5 → (((p4 → ((p3 ∧ ((p5 ∧ p4) ∨ ((p1 ∧ p4) ∨ True))) → p3)) ∨ ((False ∨ p3) → True)) ∧ p3))) → ((True → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135316496189980808960911279679 : ((((p3 ∧ (True ∨ (p4 ∧ ((p1 ∧ (((p1 → p2) ∧ p1) ∧ p2)) ∧ p4)))) ∨ (p1 ∧ p1)) ∧ ((p1 → p1) ∧ p3)) ∨ ((p4 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657821997557304641978012772529 : ((((False ∧ (((((((p3 → p3) ∨ p5) ∧ (p1 ∧ p3)) → (((p2 ∨ p3) ∧ p1) ∨ p3)) ∧ p3) ∨ (p1 → p3)) → p1)) ∨ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157435594016927356554493238533 : (((p4 ∧ (((p4 ∧ p3) → ((p4 ∧ False) ∨ (p5 ∨ p5))) ∨ (False ∨ (p5 → p2)))) ∧ (p1 → p3)) ∨ (True ∨ (False → (p2 → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175367609958715010222204320869 : ((True → ((((True ∨ p2) ∨ (p2 → (True ∨ ((True → p1) → True)))) → p4) ∧ False)) → (p5 ∧ ((((False ∧ True) → p3) ∨ p4) → (p1 ∧ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h8 := h1 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h12 := h1 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17
  case inr h18 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h20 := h1 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172696442675764168712965802445 : (((p4 ∧ p5) ∨ (p2 → ((False ∨ ((p1 ∨ p1) ∧ p3)) ∨ ((p2 ∨ False) ∨ p5)))) ∨ (p5 → (p1 → (p2 ∧ (((p4 ∨ p5) → p3) ∧ False))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_153742716216059643179387357022 : ((p3 → (False ∨ (((p1 ∨ (True ∧ ((True → p5) ∧ ((p1 ∨ (False ∧ False)) ∨ (p5 ∧ p4))))) ∨ p3) → p2))) → ((p2 → (p5 ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192614645743505782838601952591 : (((((p1 ∨ (False → False)) → (p3 → p3)) ∧ p1) → p5) → (p2 → ((p4 ∨ ((p2 ∧ ((p4 ∨ ((p1 ∧ p1) ∧ p1)) ∨ p1)) ∨ p3)) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328275639799482886258860394002 : (True → ((((p2 ∨ ((((p4 → p3) ∨ p1) → p1) ∨ True)) → (((p5 → p1) ∧ p4) → (p1 ∨ p2))) ∨ p3) ∨ ((False ∧ p1) → (p4 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773330547733008891138505978202 : (((False ∨ ((True ∧ (False ∧ (p3 ∧ ((((True → True) ∨ (((False ∨ True) ∧ p4) → p3)) → (((p3 ∨ True) ∧ p5) ∧ True)) → p1)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677905890291338244444198247181 : ((((((p2 → False) → (p3 ∧ ((False ∧ (p3 ∨ p4)) ∨ ((p3 ∧ (False ∧ p4)) ∨ p4)))) ∨ (p3 ∧ p3)) ∨ (p1 → (p3 → (p1 → p1)))) ∨ False) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38418765415957621753845803849 : (((((p2 → p4) ∨ ((((p2 ∨ p5) → p4) → (p2 ∧ (False ∨ p1))) ∨ True)) ∧ (p3 ∧ (p5 → ((p5 ∧ (p2 ∧ p1)) ∨ p1)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3318944708614854111819828339 : ((p3 ∧ p5) → ((p3 ∧ (True ∨ (p2 → (p2 ∨ p4)))) → (((((((True ∧ p3) → False) ∨ p5) ∨ True) ∧ (p3 → True)) ∧ p4) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115320721791224416445630248394 : (((((True ∧ p4) → p5) → (True ∨ ((False ∧ p4) ∨ p4))) → ((p2 ∨ (((p3 ∧ p3) → False) ∧ (p3 ∧ p1))) ∨ (p1 ∧ False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171772721202841371434563401452 : ((((p4 ∨ (((p3 → p2) ∨ (p2 ∧ p3)) ∨ ((p1 ∧ True) ∧ p1))) → False) → p1) ∨ (True ∨ (p4 ∧ (p4 ∨ (p2 → ((True ∧ p1) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314947112993224347374472614099 : (p3 ∨ (((((True → p2) ∧ (p1 → (p5 ∧ p3))) ∧ p4) → p5) → (p1 → ((p5 → (p2 ∨ (False ∧ True))) ∨ (True → ((p3 ∧ False) → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118270916429117397543423391152 : ((p1 ∨ (((p5 → (p4 → p3)) ∨ (True → False)) ∨ ((p2 ∨ p1) ∨ (p3 → (p3 → (((p4 ∧ p5) ∧ True) ∧ (True ∨ p1))))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42847488810817191432489244175 : (((p2 → (((((((p1 ∨ p5) → (p2 ∧ (p4 ∨ True))) ∧ False) → True) ∧ (p2 ∨ (p5 ∨ ((True ∧ p4) → p3)))) ∧ p5) → False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44858503775994366465507577399 : ((((False ∨ (p1 ∨ p2)) ∨ (((((((True → ((p4 → (p5 ∧ p2)) ∨ p4)) → False) ∨ (p1 ∨ True)) ∨ p4) → False) → p4) → p4)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217855251932781167102720695123 : (((True → (False ∨ p1)) → False) → ((p5 ∧ (True → (p4 ∧ ((False ∨ p4) → (p1 → (p2 ∨ p5)))))) ∨ (((p3 → True) ∨ False) → (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914143746836071297750164085601 : ((((((p2 ∨ (p1 → (p5 → False))) → (((False → (p2 ∧ p4)) ∨ p4) → p5)) → True) ∧ (True ∧ (True → (p3 ∧ ((p2 ∧ False) ∧ False))))) → p4) ∧ True) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116295951947118715081943313848 : (((p5 ∨ (p3 → p1)) ∨ ((p4 ∧ ((True ∧ (False ∧ ((p3 ∨ ((p2 → (p2 ∨ (p3 ∧ p3))) ∨ p1)) ∨ p3))) ∨ p4)) ∨ False)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774646473270694807684359397611 : (((False ∨ (((p4 → (p1 ∨ (p5 ∨ (p3 ∨ False)))) ∨ (p4 → False)) ∨ ((p5 ∨ p5) → (p3 ∨ ((True → ((p4 ∧ p2) ∧ p4)) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51253254831873637845334942887 : ((((True → p3) ∧ (p4 ∧ (p5 ∧ ((p1 ∧ ((p2 ∧ p1) → (p5 ∧ (False ∨ p3)))) ∨ p1)))) ∨ (p5 ∨ ((p4 ∧ (p1 ∨ False)) → p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323500788886903907383069890142 : (p5 ∨ ((((p4 ∨ (p3 → (p3 ∨ (False ∧ p3)))) → p5) ∨ ((False → p4) ∨ ((p2 ∧ p2) ∨ ((p4 ∧ p5) → p1)))) ∨ (False ∧ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737102419902913311728033453404 : ((((p3 → p3) ∧ ((((True ∨ (False → False)) ∧ (p2 → p5)) → p1) ∨ ((p2 ∨ ((p2 ∧ p4) → (False → p2))) → ((False → p5) → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68985256557775880735962847578 : ((p5 → (((p1 ∨ ((p2 ∧ p1) ∧ (p3 ∧ (True ∧ (p1 → (((p2 ∧ ((p5 ∧ True) ∧ True)) ∧ p1) ∨ (p4 ∧ p3))))))) ∧ p5) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123482295051925376098836099865 : (((((p1 ∨ p1) ∨ (((p2 ∨ (((p2 ∨ p4) ∧ True) → p1)) ∧ p5) → p5)) ∨ p5) ∧ (p4 ∨ ((p1 ∧ (True → p4)) ∧ p1))) → (p4 ∨ p5)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h7 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h9.left
          let h12 := h9.right
          -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h12, we can now drive its conclusion.
          let h14 := h12 h13
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Conjunctions on the left can always be decomposed.
          let h20 := h18.left
          let h21 := h18.right
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h22 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h23 := h21 h22
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- Conjunctions on the left can always be decomposed.
        let h29 := h27.left
        let h30 := h27.right
        -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
        have h31 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h30, we can now drive its conclusion.
        let h32 := h30 h31
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Conjunctions on the left can always be decomposed.
      let h38 := h36.left
      let h39 := h36.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114384818967608714659864592146 : ((((True ∧ (p3 ∨ (p4 ∧ ((((p3 ∨ p5) ∨ (p1 → p1)) ∨ p3) ∨ p3)))) ∧ (p5 ∧ p5)) ∨ (p2 → ((p4 → True) ∨ p4))) ∨ (p2 → p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350162693791129001266115651241 : (p4 → (((((p5 ∨ (p4 → p3)) ∧ (False → True)) ∧ p4) → (p2 ∧ ((True ∨ ((p3 → (p3 ∧ (p3 ∧ p2))) ∨ (p1 ∧ p2))) ∨ p3))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57323638333122638208111769368 : (((False ∧ (p4 ∨ p5)) ∨ (((p1 ∨ p3) ∧ (p2 → ((((((p1 → p2) ∧ ((p3 → p5) → p5)) ∧ False) ∨ p3) ∨ p4) → p2))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172830312696107514360387168632 : ((True ∧ (p3 ∨ (((p3 ∧ True) → (True ∧ (p2 ∨ ((p5 → p5) ∧ p3)))) → False))) ∨ (True ∨ (((True → ((True ∨ p5) ∧ True)) ∧ p4) ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322393661222589556317872075178 : (p5 ∨ (((((((True → (p5 ∧ True)) → p2) ∧ (p3 ∧ p1)) → (p5 ∨ p5)) ∧ p4) ∨ ((True ∨ p2) ∧ ((p5 ∨ (False ∧ p1)) ∨ True))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138461438521997969423870954258 : ((p5 → (p3 ∨ (p4 ∨ ((p1 ∨ ((True ∨ p1) ∧ ((p4 → (p4 ∨ p3)) → ((p2 ∧ p4) ∨ (False → p1))))) ∧ True)))) ∨ (p4 ∧ (p4 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230916684615904333929646263271 : (((p3 ∧ True) ∨ p1) → (p4 → (((p2 → ((p4 ∧ p3) ∧ (p4 ∨ ((False ∨ (p3 ∧ ((False ∧ True) → p3))) ∨ p3)))) → p1) ∨ (True ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757241629149122900178885655026 : (((p1 ∧ ((p5 ∨ p1) ∧ ((False → (p2 → (((p1 ∨ (p5 ∨ (p5 ∨ p1))) ∨ True) → (True → (p5 ∧ p2))))) ∧ (p3 ∨ (p1 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215795514264029595100256505572 : ((p1 ∨ (p2 ∨ (p3 ∨ p4))) ∨ (p3 → (p3 ∧ ((p1 ∨ ((((p3 ∨ p4) ∧ True) ∨ (False → ((p1 ∧ p3) → p5))) → p5)) ∨ (True ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45391606619326101360231319335 : (((p5 ∧ (((True → (((((False → p1) ∧ (p5 ∧ p2)) → ((False ∨ p1) ∧ p2)) → False) → True)) → (p4 → (True ∨ p3))) → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705735514958390775420096780644 : ((((((p4 ∨ p2) ∨ (False ∧ p3)) ∨ (p1 ∨ p1)) ∧ ((False ∨ p5) → (((True → False) ∨ p5) → ((p2 → ((p3 → p1) ∧ True)) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164872512280602969771656722387 : (((p5 ∨ (p1 → (False ∧ (p3 ∧ (p2 ∨ ((True ∧ (True ∨ p4)) ∨ (p3 ∨ p2))))))) ∨ p2) ∨ ((True → False) → (((False ∧ False) → True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_160747082214994681295399388723 : (((p5 ∧ (((p1 ∨ p4) → p1) ∧ (p4 ∨ p5))) → (((True ∨ True) ∧ (False → (p3 ∧ p2))) → True)) → ((p2 ∨ (True ∧ True)) ∨ (p5 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_612844812439433984658034242680 : (((((p1 ∧ ((((p3 ∨ ((p1 ∧ (p3 → (p2 ∨ ((False → (p2 ∧ p4)) → p4)))) → p4)) → p5) ∧ True) → p2)) ∨ (p4 ∧ p4)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313929861798593122657501899707 : (p3 ∨ (((((p3 ∨ ((p5 → (((p3 → p3) ∨ (p1 → ((p1 → p4) → (p4 ∨ p2)))) ∨ p5)) ∨ p1)) → p5) ∧ p2) ∨ p3) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_493627762136121118747624077177 : (((((p5 ∧ (p2 → p3)) ∧ p5) → (p3 ∨ (((p1 ∨ p4) → p2) ∨ (True ∨ (((((True ∨ True) → False) ∧ p1) ∧ (False ∧ p3)) ∨ p5))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352469560429712528764220511931 : (p4 → (((p5 → p1) → True) → ((p2 → ((p2 → (p1 ∨ p3)) → (p4 → True))) → ((((p3 ∧ True) ∨ p1) ∨ (p4 ∨ (False ∨ False))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159451288089621163252767022831 : ((((((p5 ∧ (p4 ∧ p4)) ∧ (p5 ∨ p5)) ∨ (p2 ∨ True)) ∧ ((p2 ∧ p2) ∨ (p5 ∧ p1))) ∧ p2) → (p1 ∨ (((p1 → p4) ∧ p5) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h34
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185519807123747768259165643245 : ((p3 ∨ (((p2 → ((p4 → (p2 ∨ p3)) → False)) → p2) ∨ True)) ∨ (p3 → (True ∧ (((p3 ∧ (p1 → ((True ∧ p1) ∨ p5))) ∧ False) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171747478579588899687104446982 : (((((False ∨ p3) → ((True ∧ (p2 ∨ (p5 ∨ (p4 ∨ p5)))) ∨ p1)) ∨ p3) → False) ∨ (False → (p1 ∧ ((p1 ∧ p1) ∧ (True ∧ (p4 → p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240417060091649110660597274115 : ((p5 ∨ True) ∧ ((((False ∨ (p3 ∧ (p5 ∨ p5))) ∧ (p2 ∨ ((((False ∨ p3) → ((p4 ∧ (p3 → True)) ∧ True)) → p2) ∨ p1))) ∨ True) ∧ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645335448272481755675915499149 : ((((p4 ∨ (((p2 ∨ ((p2 ∧ p1) ∧ (False ∨ p5))) ∧ ((((p5 ∧ p5) → (((p1 → False) → True) ∨ p5)) → False) → p4)) ∨ False)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111599746187788342176867897378 : ((((((((p4 ∧ (p3 ∨ (((((p3 ∨ False) ∨ (True → p2)) ∧ p3) ∧ p2) ∨ False))) → p2) → p2) ∧ p1) ∧ p1) ∨ p2) ∨ p1) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321754242779845526516104004324 : (p4 ∨ (p5 → ((p4 → False) → (p5 ∧ ((((p3 ∧ (((True → (p3 → False)) → ((p5 ∧ (p1 ∧ True)) ∨ p4)) ∧ True)) ∧ p5) ∨ True) ∨ p5))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257609289010425869294743401837 : ((p3 ∨ p2) → (((p2 ∧ ((((p4 ∨ p2) ∨ (p5 → True)) ∧ (p3 ∧ p1)) ∨ (True ∨ (((p5 ∧ p5) ∨ p4) ∧ (False ∧ p1))))) ∨ True) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340717972597188806684627571463 : (p2 → (((p1 ∧ ((p3 ∨ ((((p2 ∨ p1) → (p2 ∨ ((p5 ∨ p2) ∧ p2))) ∨ ((p2 ∧ (True → p4)) ∧ p3)) → False)) ∧ p5)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230695066181771057648549795944 : (((p4 → p2) ∧ True) → (((((p2 ∧ (((p1 ∧ (p3 ∧ p4)) ∧ (((p1 → p5) ∨ p3) ∧ p2)) ∧ (p5 ∨ p4))) ∨ p1) ∧ p1) ∧ p4) ∨ True)) := by
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
theorem thm_5_vars_741459926806066551726457374189 : ((((p5 ∨ p2) ∨ (((False ∨ ((p5 ∧ (p5 ∨ (p3 ∨ (p3 ∨ p4)))) → ((p3 → False) ∨ False))) ∧ ((p2 → (p4 ∧ p2)) ∨ p1)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743309132607745166400794739064 : ((((p5 → False) ∨ (((((((False ∧ (False → (True ∨ p5))) → False) ∧ False) ∨ (p2 ∧ ((p1 → p5) ∧ (p1 ∧ False)))) ∨ True) → p1) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109210362763334232056311508280 : ((False ∨ ((((True ∧ False) ∨ ((p5 → p1) ∧ (p3 ∧ False))) ∨ (True ∨ ((True ∧ False) → p4))) ∨ ((p4 ∧ (False ∧ p4)) ∨ p3))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757493657413598025197113307590 : (((p1 ∧ (False ∧ (p2 ∧ (((p4 → True) ∧ p3) ∧ ((p5 ∧ (p4 → p3)) ∨ (True → ((((True ∧ p4) → (False ∨ p4)) ∧ True) ∨ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167737851023988175034222149497 : ((((False → ((p2 ∨ p3) → p1)) ∨ (p5 → (p3 ∨ (p1 ∧ p5)))) ∨ ((p4 → p3) → p3)) → (p3 → (p4 ∨ ((False ∨ (p2 ∨ p2)) ∨ p3)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47403464385379711826291764178 : (((True ∧ (p3 ∧ ((((p1 → ((p2 → ((p4 ∧ ((False → p2) → (p2 → True))) → p4)) ∨ p3)) ∧ p2) ∨ p5) → p3))) ∨ (False → False)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58302732610808397432500084032 : (((True ∨ p3) ∧ (p5 ∧ (((((((((p1 → p1) ∨ True) ∨ (p5 ∨ p1)) ∨ ((p4 ∨ False) ∧ p1)) ∧ True) → p3) ∧ p2) → p5) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746795485416846484284469051934 : ((((p3 ∨ p4) → (p3 ∧ ((p1 ∨ (((((p5 ∧ (((p3 ∧ True) → p2) ∨ p2)) ∨ p1) → (p1 → p4)) ∧ p2) ∧ p1)) ∧ (p3 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717892932484883872521212366672 : (((((p2 ∨ (p5 ∧ p2)) ∧ False) ∨ ((p2 ∧ ((p3 ∧ p2) ∨ (((((False → p5) ∧ (p1 → p1)) → (p5 ∨ p2)) → p4) → p3))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667533322314885545377802191199 : ((((False ∧ ((False → p2) → ((((p3 → p5) → (p5 ∨ ((p1 ∧ p2) ∧ p1))) ∨ ((p1 ∧ p1) → p2)) ∧ p2))) ∧ ((p2 → p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737588541323365291882974868510 : ((((p5 → p1) ∧ (p3 ∨ (((p4 ∨ (p5 ∧ (False ∨ (p1 ∧ False)))) ∧ (p5 → (((p1 → False) ∨ p2) ∧ p4))) → ((False ∧ p2) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117191789944381052527246460352 : ((True ∧ ((((p1 ∨ p5) ∧ True) ∧ ((((p5 ∧ p1) ∧ (True ∨ p3)) → p1) ∨ (False ∧ p1))) ∧ (((p3 ∨ p4) ∨ p1) ∧ p3))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775809167571897445837492326601 : (((False ∨ (p5 ∨ ((p5 ∨ ((p2 ∨ p2) ∨ (p2 ∨ (True ∨ (p5 ∨ (p2 ∧ p5)))))) ∨ (((p4 ∨ True) ∨ p1) → ((False ∧ p3) ∨ False))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141279610626893653992174416455 : ((((True ∧ (False → False)) → p2) ∧ (((p2 ∨ ((False ∨ False) ∧ (p4 ∧ True))) → (p5 ∨ (p1 ∧ p4))) → (p4 → False))) → (p1 → (p2 ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∧ (False → False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h10 : (True ∧ (False → False)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h11
    -- False on the left can always be used.
    apply False.elim h11
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h12 := h8 h10
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657999938250337245427171731011 : ((((p2 ∧ ((p4 ∧ (p1 ∧ (((p2 → p4) ∨ False) ∨ p2))) → (((p4 → p4) ∨ True) → (p4 → ((p3 → False) ∨ p5))))) ∨ (p1 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1765659557871171562872001691 : (((((p1 → (((p2 ∨ (((True ∨ True) ∧ p5) ∨ p3)) → p1) → False)) ∧ (p3 ∧ p4)) → (p1 ∨ p2)) ∨ True) ∨ ((p1 → True) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648661728408889150849822833940 : ((((((p2 ∧ True) ∧ ((((((p5 ∧ (((p2 ∧ False) ∨ p2) ∧ (p1 ∧ p3))) ∨ p1) ∨ p2) → False) ∧ p2) ∨ False)) ∨ True) ∧ (p5 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108156147728054068166391440153 : (((False → p2) → (p2 → (((p1 → ((p2 ∨ True) ∧ True)) → p4) ∨ ((((p5 ∧ p3) ∧ ((p1 ∨ p1) ∨ p5)) → True) ∨ False)))) ∧ (p2 ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597746458783459726667232983782 : (((((p1 ∨ (p2 ∨ (p5 ∨ True))) → (((p2 ∧ p4) ∨ True) ∨ (p5 → ((((p1 ∧ (p5 → p2)) ∧ p4) → p2) → (p3 → p1))))) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113418304045078102587377785762 : (((((p1 → (p4 ∨ (p5 ∧ (p4 ∧ (p2 ∨ p1))))) → (p1 ∨ ((p5 ∨ ((p2 ∧ p2) ∧ p4)) ∨ True))) ∧ p1) ∨ (p4 → p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668456913605317971784570220811 : ((((((False ∨ (p1 ∧ ((((p1 → p2) ∨ p3) ∧ (p2 → (p1 ∧ (p1 ∧ p3)))) ∧ (p5 ∨ p5)))) → p4) ∧ p2) ∨ ((p1 ∧ False) → False)) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65528190529180834474070592421 : ((p3 ∨ (p3 ∨ (((False ∨ (p5 ∧ False)) → (p2 ∧ p5)) → (((False ∨ p3) ∧ (p4 → ((p4 → (False ∨ (p1 → p5))) → p1))) ∨ True)))) ∨ p5) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200754650440336751887011128802 : ((p3 ∧ (p3 → (((p3 ∨ p2) → p4) → p3))) → (p3 ∧ ((((((p4 ∧ p4) → p1) ∧ p3) ∧ True) ∨ (p2 → p2)) ∧ (p5 → (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58612505585099829633649964459 : (((False → p2) ∧ (p4 ∨ (p5 ∨ (((p2 → p2) → ((p3 → (False ∧ p3)) ∧ ((((p1 → False) → (p1 → p2)) ∨ True) → p1))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



