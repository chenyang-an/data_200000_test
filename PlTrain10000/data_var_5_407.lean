variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654977103711808503483734070866 : ((((((p4 → (p3 ∧ p3)) ∨ ((p2 ∧ (p4 ∨ ((p2 → (((p5 ∨ p3) ∨ p5) → (p3 ∧ p1))) ∧ True))) ∧ True)) → p1) ∨ (p1 → p1)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638615387046975131746572392577 : (((((p3 → ((False ∨ p1) ∨ (False → p5))) ∨ ((((p2 ∧ p1) ∨ (p1 → ((p1 ∧ (p2 → (p3 ∨ p5))) ∧ p2))) ∨ p1) ∧ p5)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126739376733988518654008796112 : ((p4 ∧ ((p3 → False) ∧ (((p1 ∨ ((((False ∨ False) ∧ True) ∧ ((p5 → (False → (p4 ∨ p5))) ∧ p5)) → p5)) ∨ p1) ∨ p2))) → (p3 → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h16 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h17 := h5 h16
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47988549493014348101909472878 : ((((((p4 ∨ (((p2 ∨ p3) ∧ p2) ∧ ((p3 ∨ p5) → p4))) ∨ p4) ∨ p1) ∧ ((True ∨ True) ∨ (p5 ∨ (p5 → True)))) → (p1 ∨ True)) ∨ p3) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h3
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
          -- Disjunctions on the left can always be decomposed.
          cases h10
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
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h14.left
        let h17 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h19 =>
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h24 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
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
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h30 =>
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
      cases h3
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h39 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h40 =>
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h41 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h42 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
    case inr h43 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h44 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39
      case inr h45 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54671892985198880089790823977 : (((((((p2 ∧ p2) → p1) ∧ p1) ∨ True) → p5) → (((((((p2 ∧ ((p1 ∨ p1) → p3)) ∧ p1) ∨ p5) → p4) → True) → False) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342081611145859966655849252071 : (p2 → ((p2 ∨ ((((p3 ∧ (p3 ∨ p4)) → (((True → (p1 ∧ (p1 ∧ p4))) → (p4 ∧ False)) → p2)) ∧ True) ∧ p3)) → ((p1 ∨ False) → p1))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792814479770955757272735373474 : (((True → (((True ∧ True) ∧ p1) ∨ (((p3 ∨ (p4 ∧ p3)) ∧ (((p3 ∨ False) → (True ∨ p3)) ∨ (((p2 → p2) → p3) ∨ False))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46398309893981067743137577251 : (((((p5 ∨ ((p2 ∧ p5) ∧ (p5 ∧ p1))) → p4) ∧ (False ∨ (((p3 → p4) ∧ (((False ∧ p4) ∨ True) ∧ p5)) ∧ p1))) ∧ (p5 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137412182863089324572482989828 : ((p4 ∧ (((((True ∧ (p4 → (p5 ∧ (((p2 ∨ p4) → p2) → p1)))) ∧ (p1 ∧ (p5 ∧ p4))) ∨ p5) ∨ p4) ∧ p2)) ∨ ((p4 ∧ False) → p1)) := by
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
theorem thm_5_vars_329237748922757078075796148703 : (True → ((p1 ∨ (False → False)) ∧ (((False ∨ p2) → (((p4 → p1) ∨ p3) ∧ p5)) → ((p1 ∨ (False ∧ p5)) ∨ (p5 ∨ (p1 ∨ (p1 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158012615275625790839555994906 : ((((p5 ∨ ((p2 ∨ True) ∧ True)) ∨ p5) ∧ ((p4 ∧ (((p5 ∨ p4) ∧ (p1 ∧ False)) ∨ p4)) ∨ True)) ∨ ((((p5 ∧ True) ∨ p4) ∨ p5) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749179007576978303130810625516 : ((((p5 → p2) → ((p2 → ((p1 ∨ False) ∧ ((p2 ∨ (((((False ∨ p4) → p2) ∧ p2) ∧ p4) ∧ p2)) ∧ (False ∧ p3)))) ∨ (True ∨ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_346836182108470746551150454901 : (p3 → ((((False ∨ p4) → p3) ∨ ((((True ∨ p5) ∨ p2) ∨ p3) ∨ (p1 ∨ (p4 → ((p1 → p4) → True))))) → ((False ∧ p1) ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h9 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h10
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h12
            -- False on the left can always be used.
            apply False.elim h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157748177053832711992156069090 : (((((p5 ∧ p1) ∨ (((p3 ∧ p3) ∨ p4) ∧ False)) ∧ (True ∨ True)) ∧ ((p3 ∨ p5) → (p4 ∧ True))) ∨ ((False → ((p2 ∨ p5) ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187391670817765476932077186331 : ((p4 ∧ (((p4 → False) ∨ ((True → (p2 → True)) → p3)) → p1)) → (((True ∧ (((p5 → p1) ∨ p4) ∨ (False ∨ True))) → p2) → (p4 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (True ∧ (((p5 → p1) ∨ p4) ∨ (False ∨ True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655437972599898639427403305010 : ((((((p5 ∨ False) ∨ ((p3 → (((p3 → p2) → p1) ∧ True)) → (((p5 → p5) ∨ p4) ∧ (False ∧ p4)))) ∨ (p5 ∧ p5)) ∨ (True ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123501371618364444246091625978 : ((((p2 ∧ (p4 ∨ (((True ∨ (True ∨ True)) ∨ p4) ∨ p5))) ∨ (True ∨ (p4 ∨ True))) ∧ ((False ∧ p5) ∨ (p5 → (False ∨ p4)))) → (p5 ∨ True)) := by
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
      cases h3
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h9
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h3
            case inl h16 =>
              -- Conjunctions on the left can always be decomposed.
              let h17 := h16.left
              let h18 := h16.right
              -- False on the left can always be used.
              apply False.elim h17
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
              cases h3
              case inl h22 =>
                -- Conjunctions on the left can always be decomposed.
                let h23 := h22.left
                let h24 := h22.right
                -- False on the left can always be used.
                apply False.elim h23
              case inr h25 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
            case inr h26 =>
              -- Disjunctions on the left can always be decomposed.
              cases h3
              case inl h27 =>
                -- Conjunctions on the left can always be decomposed.
                let h28 := h27.left
                let h29 := h27.right
                -- False on the left can always be used.
                apply False.elim h28
              case inr h30 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
        case inr h31 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h32 =>
            -- Conjunctions on the left can always be decomposed.
            let h33 := h32.left
            let h34 := h32.right
            -- False on the left can always be used.
            apply False.elim h33
          case inr h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- False on the left can always be used.
          apply False.elim h38
        case inr h40 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h36
  case inr h41 =>
    -- Disjunctions on the left can always be decomposed.
    cases h41
    case inl h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- False on the left can always be used.
        apply False.elim h44
      case inr h46 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h48 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h49.left
          let h51 := h49.right
          -- False on the left can always be used.
          apply False.elim h50
        case inr h52 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h53 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h54 =>
          -- Conjunctions on the left can always be decomposed.
          let h55 := h54.left
          let h56 := h54.right
          -- False on the left can always be used.
          apply False.elim h55
        case inr h57 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54457209047626135806987593473 : (((((p3 ∨ p1) → ((p3 ∨ False) → p1)) → False) ∨ (False ∨ ((p1 ∨ p1) → (((False ∧ (p5 → True)) → ((True ∨ p5) ∨ p1)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710727983463010762832015668865 : ((((((p3 ∧ p3) ∨ p2) → (p3 ∨ False)) ∧ (((((p3 ∨ p4) → (p4 → True)) → (True ∨ False)) → ((p1 ∧ (p4 → True)) → p5)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37671270405718662709396499757 : (((((p4 ∨ (True ∧ ((False → ((p3 ∧ False) → (p5 → ((((p4 ∧ p4) → p5) ∧ p2) ∧ (p5 ∧ True))))) → p2))) → p2) → p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37470559165055303400366415680 : ((((((p4 ∨ False) ∨ (p5 → (p4 ∨ False))) ∧ (((p2 ∧ False) ∨ (False ∨ (True → p3))) → (((p1 ∨ p4) → False) → p4))) ∨ False) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322280961768692352958540347857 : (p5 ∨ (((((p5 ∨ (p2 ∧ p3)) ∧ ((p1 → (p4 → (((p4 ∨ (p4 ∧ p1)) → p4) ∧ (p3 → (p1 ∧ p4))))) ∨ p4)) ∨ True) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354914419405990491323697651257 : (p5 → ((False ∨ (p1 ∨ ((((p1 → (p4 ∨ p4)) ∨ ((True → (p2 → (((p1 ∧ p4) ∨ True) → (False → False)))) ∨ p3)) ∧ False) ∨ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185358290746283947582007489798 : ((p4 ∧ (p3 ∧ (p5 → (True ∧ (p3 ∨ (p3 ∨ (False ∧ False))))))) ∨ (((((p5 → (p3 ∧ p4)) ∨ ((p5 ∨ p4) → True)) → p4) ∧ p2) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 → (p3 ∧ p4)) ∨ ((p5 ∨ p4) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119311575405605970949761381616 : ((p3 → (((False ∨ (((p3 → (True ∨ p5)) ∨ p2) ∨ ((False ∨ (True ∧ (p5 → False))) ∨ p5))) ∨ p3) ∧ ((p5 ∨ p1) ∨ p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41906677418154832399688424113 : (((((p2 ∨ p2) ∨ p2) → (((p4 ∧ (((((p5 ∨ True) ∨ p3) → (p3 ∧ p5)) ∨ ((p5 ∨ p5) ∧ p5)) ∧ p1)) ∧ True) ∨ True)) ∨ p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_116413852102427531038049123114 : (((p1 ∨ (False → False)) → ((((p3 ∨ p3) ∨ (p5 → False)) → (p4 ∧ p5)) ∨ (((p5 → (True ∧ False)) ∨ p2) ∨ (False → p5)))) ∨ (False ∧ p2)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310693862674062384511595968328 : (p2 ∨ ((p2 → ((p4 ∨ p3) ∨ p1)) → (p2 ∨ ((p4 ∧ (p2 ∨ p3)) → (p5 ∨ ((p3 ∨ p5) ∨ (p5 → ((p5 ∧ (True ∨ True)) → p2)))))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207509108092601561147649647835 : (((((p3 → True) ∧ p5) ∧ p2) → False) → ((p1 ∨ (((p5 ∧ p2) ∧ p2) ∨ (((p2 ∨ ((False ∧ (True → p1)) → p2)) ∨ True) ∨ p4))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39901636371357569835839167068 : (((p2 → (p2 → ((False → (p4 ∨ ((((p4 → False) ∨ (p2 ∨ (False → p5))) ∨ ((False ∨ (p2 → p2)) ∨ p1)) → p4))) → p5))) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232388457424996450806853512114 : (((p5 → p2) → False) → (((False ∧ (((p1 ∧ p3) ∨ (((True → p4) ∧ p1) ∨ ((p1 ∨ p4) → p2))) ∧ p5)) ∨ (False → (p3 → p4))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171560031078564230197164928561 : ((((p2 ∧ (False ∨ (((p5 ∧ False) ∧ (p3 ∨ (True ∧ p3))) → False))) → False) ∨ p3) ∨ (p2 → ((p3 → (True ∧ (p4 ∧ p4))) ∨ (p2 ∧ p2)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67996932813055894628124034793 : ((p2 → ((p1 ∨ p4) ∨ ((((p5 → (p3 → p1)) ∨ (p3 ∨ (p3 ∧ p3))) → (p3 ∨ p5)) ∧ ((((False ∧ p2) → p1) ∧ p4) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157454838509969383309634225122 : (((((((p2 → p3) ∧ (True → (p4 → (p5 → p3)))) ∨ p5) → (p4 ∨ p2)) ∧ p4) ∨ (p5 ∧ True)) ∨ ((p1 ∧ False) → ((p5 ∧ True) ∧ p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8930715669864652564561589992 : ((((((p5 → p1) → p5) → ((((False ∨ False) → p5) → (p1 ∧ p3)) → ((p1 ∨ p1) → p5))) → (((p5 ∧ p1) ∧ p4) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309405877324926013074242872167 : (p2 ∨ ((p1 → ((((((p3 → p5) ∨ True) ∧ (((p3 → p5) → (p1 → p4)) ∨ p5)) → ((p2 ∨ p4) ∧ p3)) ∧ p3) ∨ p1)) ∨ (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608231581848326408122422165754 : (((((((((p2 → p1) ∨ (True ∨ ((True ∧ True) → (True ∧ (p3 ∧ p4))))) → ((True ∨ (p4 → p1)) → p1)) ∧ p3) ∨ p2) ∨ p5) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702970539965837687643204528934 : (((((p3 ∨ (p1 ∧ p3)) ∨ (((p3 ∧ p5) ∨ p3) ∨ p5)) ∨ ((p1 ∨ (True ∨ (((p2 → p2) → p4) ∨ (True ∨ (p4 ∨ p3))))) ∨ p1)) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114623677809479631189168725118 : (((((p4 → True) → ((p5 ∧ p5) ∧ (p5 ∨ (((p1 → p5) ∧ p4) ∨ p5)))) ∧ p3) ∨ ((False → (p4 → p4)) ∨ (False ∨ p5))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219310822213288041413325632400 : ((p2 ∨ ((p1 ∨ p4) → p1)) → ((((p3 → (p4 ∧ ((p2 → (p3 ∨ (p3 → p1))) ∨ p3))) → p1) ∧ (p1 ∨ ((p2 ∧ p1) → True))) ∨ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350454664752006594316629118119 : (p4 → (((((p1 ∨ False) ∨ (p2 → ((p2 ∧ ((((p1 → p1) → p4) ∧ p2) → p1)) ∨ p2))) ∧ ((p2 ∨ False) ∨ (p2 → True))) → False) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((p1 ∨ False) ∨ (p2 → ((p2 ∧ ((((p1 → p1) → p4) ∧ p2) → p1)) ∨ p2))) ∧ ((p2 ∨ False) ∨ (p2 → True))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77505892063153657324894585706 : ((((p5 → p2) → (((p5 ∧ (p3 ∧ ((p5 ∨ True) → (p1 ∧ p4)))) ∧ (p2 → ((p5 ∧ ((p3 → p2) → p4)) ∨ p3))) ∨ True)) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → p2) → (((p5 ∧ (p3 ∧ ((p5 ∨ True) → (p1 ∧ p4)))) ∧ (p2 → ((p5 ∧ ((p3 → p2) → p4)) ∨ p3))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43699549536345040840304238415 : (((((((True → p4) ∧ True) ∧ (p1 → p5)) ∨ ((((p5 ∧ p4) ∧ ((p5 ∧ p5) → ((p4 ∧ p5) ∧ p4))) → p4) ∧ p1)) → p2) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157164214840755317493718315928 : ((((p3 → (((True ∨ ((p3 ∨ p1) → (False ∨ (False ∧ (p2 ∨ p3))))) ∨ p3) ∨ True)) ∨ p1) → p3) ∨ ((((True ∧ p4) → p3) → True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141002860627984914151844270740 : (((p5 ∨ ((p4 ∧ ((True → False) ∨ (p4 ∧ p1))) ∧ p2)) → (((p2 ∧ ((p4 → p3) ∧ p2)) → True) ∧ (p1 ∨ p2))) → ((p3 → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44860904636464069603138530114 : ((((p2 ∨ (p1 → True)) ∨ (((((False ∨ ((p3 → (True → p1)) ∨ p4)) ∧ p3) → False) → ((p5 ∧ False) ∧ (p5 ∧ False))) ∨ p3)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200573666987153656445166963513 : ((True ∧ ((p3 → ((p3 ∧ p1) ∧ False)) ∧ p1)) → (((p4 → ((p1 → p4) → p2)) ∧ ((True → False) ∧ p4)) → (p2 ∧ (p2 → (True → p5))))) := by
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
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- Implications on the right can always be decomposed.
  intro h13
  -- Implications on the right can always be decomposed.
  intro h14
  -- Conjunctions on the left can always be decomposed.
  let h15 := h2.left
  let h16 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h16.left
  let h18 := h16.right
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h21 := h20.left
  let h22 := h20.right
  -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
  have h23 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h17, we can now drive its conclusion.
  let h24 := h17 h23
  -- False on the left can always be used.
  apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326150022294594802870715526795 : (p5 ∨ (p1 → (p4 → ((((False → p1) ∧ (p4 ∧ (False → p1))) → ((True ∨ p1) → (((p5 ∧ p4) → p1) → (p5 ∨ p5)))) ∨ (p3 → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352262452529856353654614531345 : (p4 → (((p1 ∨ (p1 → True)) ∧ p4) → (((((p2 ∨ ((True ∧ p5) ∧ True)) → p1) ∧ ((p1 ∧ ((True ∧ p1) → p1)) ∨ False)) → False) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191367007923061543441568160354 : (((True → p2) ∨ (((p2 ∧ True) ∨ (p3 ∧ p4)) → p4)) ∨ (p3 ∨ (p4 ∨ ((p3 ∨ ((p4 ∧ (p1 → False)) → (p3 → (p3 → True)))) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42628665734439172243466789655 : (((p3 ∨ (((p3 ∧ p5) → True) → (p3 ∧ (((p4 → (((p3 ∧ p1) ∧ p1) → False)) ∧ False) ∧ (p4 ∨ (p1 ∧ (False ∧ True))))))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116004448398635513323746783282 : ((((p5 ∨ p2) ∧ (p5 ∧ True)) → ((p5 → p1) → ((((((False ∧ False) → False) → p3) ∨ ((True ∧ p1) ∨ p2)) ∧ p5) ∨ p1))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h6 := h4.left
    let h7 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40912399095793337570392403938 : ((((False ∨ (((((True → (p2 ∧ p5)) ∨ (True ∨ p2)) ∨ p3) ∨ p1) ∧ ((False ∨ p4) ∨ (p4 ∨ (p5 ∧ False))))) ∧ (p1 ∨ p3)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303883040160293479409198839194 : (p1 ∨ (((((((((p2 → p4) ∨ p2) ∧ ((p2 ∧ p5) ∧ p1)) ∧ p4) → p1) ∨ (p1 ∨ p4)) ∧ p5) → ((True → p1) ∨ (p4 → p4))) ∨ p1)) := by
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
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317755512314148457424307610536 : (p4 ∨ (((p4 ∧ (((p4 ∨ p4) ∧ ((p1 ∨ p3) ∧ (p4 ∨ ((p4 ∨ (True ∧ p1)) ∧ p1)))) ∧ p2)) → (((p5 → p2) → p1) ∨ True)) ∨ False)) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h7.left
    let h31 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Conjunctions on the left can always be decomposed.
          let h39 := h38.left
          let h40 := h38.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h41 =>
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h42 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h43.left
        let h45 := h43.right
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h47.left
          let h49 := h47.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305780713164623410623403947649 : (p1 ∨ ((p3 ∧ (((p2 → (p4 ∧ True)) → p5) ∨ False)) ∨ (p1 ∨ (p3 ∨ (((p4 ∧ p1) → p4) ∨ (((p1 → False) → (p3 → p2)) → True)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42641669353341620136438568485 : (((p3 ∨ (p3 → ((((False ∨ (p3 → ((p5 ∨ True) ∧ ((p1 ∧ False) ∧ (p1 ∨ False))))) → True) → ((False ∧ p3) ∧ True)) ∨ p1))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346342430435596848809353906346 : (p3 → ((((p2 → ((p5 ∧ True) ∧ (p2 ∨ p3))) ∨ p1) → (((True ∧ (p1 ∧ p5)) → (True → p5)) → ((p2 → p5) → p5))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123671194727621721815188908739 : ((((p5 ∧ p2) ∨ ((False → (p3 ∨ (False ∧ ((p1 ∨ p3) ∧ True)))) ∧ (p3 ∧ p1))) → (((False → p4) → p3) ∨ (p3 → p1))) → (p4 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731977501477073496008254862104 : ((((True ∧ True) ∧ ((((p1 ∧ True) ∧ False) ∧ (((p1 ∧ p3) ∧ ((p4 ∧ p3) → (p3 ∨ ((False → p3) ∨ p5)))) ∧ p3)) ∨ (True ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779437640599648887581213710354 : (((p2 ∨ (((((p5 ∧ p2) ∧ (p3 ∨ p5)) ∧ (p3 ∨ (p1 → (False → ((p1 ∨ p4) ∨ ((p4 → p5) ∧ False)))))) ∧ (p4 ∨ p5)) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41271451106576405594814148145 : ((((p2 → (p4 ∧ ((p1 ∧ ((p5 ∧ (True ∨ ((p5 ∨ True) ∧ (False ∧ p3)))) ∨ False)) ∧ p2))) ∨ (p3 ∨ (p3 ∨ (True ∨ p2)))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45348451960018601889271028252 : (((p4 ∧ (((False ∨ (((p1 ∨ (p2 → True)) ∧ False) → ((p4 ∨ ((p2 → False) ∧ p5)) ∧ p3))) ∧ ((p2 ∧ p3) ∨ p4)) ∨ True)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198636152795415245987489361942 : ((p3 ∨ ((((p2 → p4) ∨ p5) → p1) → p2)) ∨ (((True → p3) ∧ (True → ((p3 ∨ (True → ((True ∧ p1) ∨ p4))) → (p3 ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66283024414794564786666420457 : ((p5 ∨ ((p4 ∧ True) ∧ ((True ∧ p5) → (False ∧ (p2 ∨ (p5 → ((True → (p2 ∨ p1)) ∨ (((p5 ∨ p5) ∧ (p1 ∨ True)) → p5)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114923805705545810163057526846 : ((((((p2 ∧ p5) ∨ (p2 → ((False ∧ p2) ∨ p5))) ∧ p2) ∧ (True ∨ True)) → (((False ∨ p5) ∨ p5) ∧ (p3 ∨ (True ∧ p2)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191918653830724372748305849851 : ((p5 ∨ (p2 → ((((p3 ∨ p2) ∧ False) ∧ p4) ∧ p5))) ∨ (((False ∨ ((True → p1) ∨ p4)) ∧ p1) → (p5 → ((p3 ∧ True) ∨ (p5 → p5))))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114475082292395002222074982217 : ((((p2 ∨ (p5 ∧ (((True → False) → (p2 ∨ ((p2 → True) ∧ p1))) ∨ (p5 → p4)))) → p1) → (((p1 ∨ p2) ∨ p3) ∨ False)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10236438695574337352437754444 : (((p2 ∨ (p1 ∨ (((((p2 ∧ p1) ∨ (p5 → p1)) ∧ p3) ∨ (p1 ∧ p4)) ∨ ((False ∨ (p3 ∨ (p1 ∨ False))) → (p5 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150196145143269301342503879938 : ((p2 → (((((((p5 → False) ∧ (False ∨ p2)) ∨ ((p2 ∨ p5) ∧ False)) ∨ p4) ∨ p1) → (True ∨ False)) → p4)) ∨ ((p4 → (p2 → p2)) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702048777899477397013912903959 : ((((False → ((True ∨ p1) ∧ ((p3 ∧ (p1 ∧ p2)) ∧ p1))) ∧ ((p1 ∧ (p2 → (((p4 ∨ (p3 ∨ p5)) ∨ p3) ∧ p4))) ∨ (False → p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65738682911692652325187575645 : ((p4 ∨ (((((False → ((p1 ∧ (p2 ∧ (p2 ∨ p4))) ∨ (p4 ∧ (p1 ∨ p3)))) → (p1 ∨ p5)) ∧ p1) ∧ True) ∨ (p3 → (False ∨ True)))) ∨ p2) := by
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
theorem thm_5_vars_149657130971206220027104963223 : ((p4 ∧ ((True ∧ True) → ((False → p3) ∧ ((p3 ∧ False) ∧ ((True → ((False ∧ (p2 ∨ True)) ∧ p3)) ∨ p5))))) ∨ ((False ∧ (True ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137165150554726005937405864081 : ((False ∧ ((True → ((p1 → p3) ∨ ((p1 → (((p4 ∧ p5) ∨ p4) → ((p2 ∨ (p4 ∨ p4)) ∧ True))) ∧ p3))) → p1)) ∨ (p3 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637979795897194553409585108592 : ((((((((p4 ∧ (p1 ∧ True)) → p2) → p1) ∨ p5) ∨ ((p4 ∧ (((p3 ∧ (p3 → False)) ∨ True) ∧ p2)) → ((p2 → p3) ∨ p3))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147190964561149849352860427011 : (((p4 ∨ ((p3 ∨ p3) → ((((p4 ∧ p1) ∧ p2) ∨ (p1 ∨ (False ∧ (p5 → p4)))) ∧ (p5 ∨ p3)))) ∧ p4) ∨ (p2 → (p2 ∨ (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942997288331421633116717507401 : (((((p2 ∧ False) ∨ (True → False)) ∧ (((((p2 ∧ (p2 ∧ p1)) → (p1 ∨ (False ∨ (p5 ∧ (p3 ∨ True))))) ∨ False) ∨ (p1 ∨ p5)) → p4)) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258969720790865378232756838495 : ((True → p3) → (((p3 → (((p1 → (False ∧ p2)) ∨ p5) → True)) → p3) ∨ (((p4 → ((p1 ∨ True) → p1)) ∨ (False → p1)) → (p5 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115916989783666513547037192473 : ((((p4 ∨ p3) ∨ (p1 ∨ p5)) ∨ ((p4 ∧ p1) → (p2 ∨ ((False ∨ p1) ∧ ((False ∨ True) ∨ (False → ((False ∨ True) → p4))))))) ∨ (p1 → p2)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154908682316697392905989771423 : ((((p1 ∧ (p1 ∨ ((False → (p1 ∧ p5)) → ((p1 ∧ p4) ∨ p3)))) ∨ True) ∨ (p2 ∨ (True ∧ p4))) ∧ ((((False ∨ p2) → True) ∨ p1) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135868979130214942620645326958 : (((((True ∧ p1) ∧ (True ∨ (p3 ∨ p5))) ∨ ((p3 → p5) → p1)) ∨ (((p5 ∨ p2) ∧ p3) ∨ ((p3 ∧ p4) → p5))) ∨ (True ∨ (p5 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114632309378850839178628071009 : ((((p3 ∨ ((p1 ∧ ((True → p2) ∨ ((p1 ∧ p2) ∧ (p4 → p4)))) ∨ p4)) ∨ p3) ∨ (p3 → (((True → p1) → p5) → True))) ∨ (p2 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112780807450165910002203669672 : (((((p1 ∨ (p4 → (True ∨ (p3 → p3)))) → p3) ∨ (p1 ∨ ((p1 ∧ p4) → (((p4 ∧ (p3 ∨ p3)) ∨ p5) ∨ p5)))) → p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260040612526150153324546821951 : ((p2 → False) → (((p3 → ((p2 ∧ p5) ∧ (p5 ∨ p3))) ∧ (p1 ∨ (p4 → ((((p2 → (p4 → p4)) ∨ (p3 ∧ p1)) ∨ False) ∧ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703441321302626449124397501679 : ((((p4 ∨ ((p1 ∧ ((p2 ∧ (p2 ∨ p5)) → p4)) ∧ p3)) ∨ (False ∨ (((((p4 ∧ True) → (p3 ∨ p1)) → p4) ∨ p4) ∨ (True ∨ p5)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_179126532033363146669579929453 : ((p1 ∧ (((((p3 → True) ∨ p5) → (p2 ∧ False)) ∧ p3) ∨ (True → p4))) ∨ (True ∨ (p5 → ((False ∧ ((p1 ∧ p4) ∧ (p1 ∧ p4))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708914047449112735058564863547 : ((((((True ∧ p1) ∨ (True → p3)) ∨ (True → p5)) → (p4 → ((((False ∨ ((p1 ∨ (p3 ∨ False)) ∨ True)) → p3) ∧ (True ∧ p5)) → p3))) ∨ p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h12 : (False ∨ ((p1 ∨ (p3 ∨ False)) ∨ True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h13 := h4 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h16 := h14 h15
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h17 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h18 : (False ∨ ((p1 ∨ (p3 ∨ False)) ∨ True)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h19 := h4 h18
    -- One of the premise coincides with the conclusion.
    exact h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247406396622744672483523381650 : ((False ∨ p2) ∨ ((((p1 → (((p3 ∨ p1) ∨ (((False → False) ∧ p3) ∧ p1)) ∧ (p5 ∧ (((p4 → p2) ∨ p3) ∧ p5)))) ∨ True) ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356347459190782570574901399288 : (p5 → (((((p4 → (p4 ∨ p4)) → (p1 ∨ p1)) ∧ ((p3 → p5) → p1)) → p3) ∨ ((p4 → (((p1 ∨ p4) → (True ∨ p1)) ∨ p1)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40348906150067048148226986598 : (((((((((False → (p1 ∧ (p5 ∧ (p1 ∧ p5)))) ∨ ((False → (p2 ∧ True)) ∧ (p5 → p3))) ∨ True) ∨ p3) ∧ True) → p2) ∨ p1) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171934233348581015189930650465 : ((((p2 ∨ ((p3 ∧ (True ∧ (p1 → (p2 ∧ False)))) ∨ p1)) ∨ p4) ∧ (p3 ∨ p3)) ∨ (False → ((p3 ∧ (p1 → p1)) ∨ ((p5 ∨ p4) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760647281186545758879871664996 : (((p2 ∧ (p5 ∧ ((((p1 → False) ∨ (p4 ∨ ((p3 → (p1 ∨ ((((p1 → p3) ∨ p5) ∨ p1) ∨ p4))) ∨ p3))) → p5) ∧ (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171535215946465270009091106090 : (((((p1 ∨ (p4 ∧ p2)) ∨ ((p3 ∨ ((p1 ∧ True) ∧ p4)) ∨ p5)) ∨ False) ∨ p1) ∨ ((((p3 ∧ True) ∨ (p5 → p1)) ∨ p5) → (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603639352432814648018957194411 : ((((p4 ∨ (((((p5 ∨ p4) → p2) → (False ∧ ((p4 ∧ (False ∧ (p1 → p4))) ∧ ((p2 → p3) ∨ (p5 ∧ p1))))) ∨ p4) ∧ False)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213579900281517415362806170466 : ((((p5 ∨ p2) ∧ True) ∨ p2) ∨ (((False → p1) ∧ ((p5 ∧ p5) ∧ ((p2 ∧ p2) → ((p3 ∧ (p1 ∧ False)) ∨ (p4 ∨ (p5 ∨ p2)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788142701714639291058566894905 : (((p5 ∨ (((p4 → (((p1 → p2) ∧ False) → (((p2 ∧ False) ∧ p3) ∨ False))) → (p3 ∨ ((((p1 → False) ∧ p5) → False) → p1))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58917356729898103274090209176 : (((p1 ∧ p1) ∨ (((((((((True ∨ True) ∧ p1) → (p4 → True)) ∧ p5) ∨ p1) → False) ∧ ((p5 → p2) → (p4 ∧ p5))) ∨ True) ∨ p5)) ∨ p2) := by
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
theorem thm_5_vars_44561236983682459534577628271 : (((((p2 → False) ∧ (((True ∧ p2) ∧ p1) ∨ p2)) ∧ ((False ∨ (p2 ∧ ((True ∧ p5) ∨ ((p5 ∨ (p3 → p4)) ∨ p2)))) ∧ p3)) → p5) ∨ p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h3.left
    let h12 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h24 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h15
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h25 := h4 h24
            -- False on the left can always be used.
            apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h27 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h26
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h28 := h4 h27
          -- False on the left can always be used.
          apply False.elim h28
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Conjunctions on the left can always be decomposed.
      let h34 := h33.left
      let h35 := h33.right
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h36.left
        let h38 := h36.right
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h39
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- One of the premise coincides with the conclusion.
            exact h41
          case inr h42 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h43 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h34
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h44 := h4 h43
            -- False on the left can always be used.
            apply False.elim h44
        case inr h45 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h46 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h45
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h47 := h4 h46
          -- False on the left can always be used.
          apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249942058627681007149651570460 : ((True → p1) ∨ (p2 ∨ (((p4 ∨ ((p4 ∨ p3) ∧ (((p2 ∨ p2) ∨ (p4 ∧ p5)) ∧ ((p2 → (True → (False ∨ p5))) ∨ p4)))) → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345672261164170890654170634221 : (p3 → ((p1 ∨ (((True ∧ p2) → ((p2 → True) → p4)) ∧ ((False ∨ (p4 → False)) ∨ (True ∨ ((True ∧ (False ∨ (True ∧ p3))) ∧ p1))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



