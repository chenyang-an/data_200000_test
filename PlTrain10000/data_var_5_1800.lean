variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161410397913341412077995699051 : ((p1 ∧ (False → (p1 ∨ (p1 ∨ ((p1 ∨ ((((p1 ∧ p4) ∧ (p4 ∨ p5)) ∧ False) → p4)) ∨ p5))))) → (((p3 → False) ∨ (p3 ∨ False)) ∨ True)) := by
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
theorem thm_5_vars_134347998835880260366854658749 : (((p5 ∧ (True → (((p4 ∨ p5) ∨ False) ∧ ((p3 ∨ ((((p2 → p5) ∨ (True ∧ p3)) → True) → True)) ∧ True)))) ∨ True) ∨ (p1 → (p3 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587776380732770640687437497693 : (((((((((((p1 → (False ∨ p4)) ∨ p5) → p1) → p1) ∨ (p3 → p1)) → ((True ∧ p1) ∧ (False → p3))) ∧ (p5 ∨ p1)) ∨ False) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216997493800294887886978129954 : (((p5 → (p3 ∨ p5)) ∧ p3) → (((False → p4) → (((((p4 ∨ (False → True)) → p5) → p3) ∨ False) → (True ∧ (False ∧ (p5 ∨ False))))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h5
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((((p4 ∨ (False → True)) → p5) → p3) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52006449917010432317915710591 : (((p2 ∧ (((p5 ∨ (p4 → p5)) ∧ p2) ∧ (False ∧ (False → (p4 → (p5 → False)))))) ∨ (((p2 ∧ p4) → True) ∧ ((p5 → p1) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117281889072116928909741401417 : ((False ∧ ((p2 ∨ ((True ∨ ((True ∨ (p3 ∧ p5)) → False)) ∧ (True ∧ (p3 ∧ (p2 ∧ (((True ∧ p2) ∨ True) ∧ p2)))))) ∨ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38705576729673238567380488231 : ((((False ∧ ((True ∨ (p2 ∨ True)) ∧ p5)) ∨ ((p5 ∧ p3) ∨ (p1 → (True → (p3 → (p1 → ((p1 → (False ∧ p2)) ∨ p1))))))) ∧ True) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689489258654089980464185305064 : ((((((True ∨ (p5 → p4)) ∨ (p2 → ((p1 ∨ p3) ∧ p3))) → ((p2 ∨ p3) ∧ p3)) ∨ ((True ∨ (p1 ∧ (True → False))) ∧ (p2 → p2))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343028489159048165709497660748 : (p2 → (((True ∨ (p3 ∨ p3)) → p5) → ((((((p5 ∨ False) ∧ (p4 ∨ p3)) ∧ True) ∨ True) → (p4 ∨ (p4 ∨ ((True ∧ p4) ∨ True)))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ (p3 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325690908170533400099565662707 : (p5 ∨ (p1 ∨ ((p1 ∧ (p5 ∧ (((p1 ∧ (True → (p1 ∧ (p3 → p4)))) → (p4 → p4)) → (False ∧ p5)))) ∨ ((False ∨ p5) ∨ (p4 → p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_861783165748062127155149273108 : (((((p2 → ((True → p2) → (((((p4 ∨ p4) → (p3 ∧ (p2 ∧ p1))) ∧ p3) → True) ∧ (p5 ∧ p2)))) → ((p3 → p5) ∨ True)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → ((True → p2) → (((((p4 ∨ p4) → (p3 ∧ (p2 ∧ p1))) ∧ p3) → True) ∧ (p5 ∧ p2)))) → ((p3 → p5) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257507269420966687971178605293 : ((p3 ∨ False) → ((True ∧ (((p2 ∨ (False ∨ p3)) ∨ (p3 → ((p1 → p1) ∧ p4))) ∧ ((p5 → p4) ∨ p4))) → (((p1 ∨ p4) ∧ False) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- False on the left can always be used.
          apply False.elim h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h20 =>
            -- False on the left can always be used.
            apply False.elim h20
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- False on the left can always be used.
            apply False.elim h23
  case inr h24 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h29 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41477225757433496804837381143 : ((((((p1 → True) ∧ ((p5 ∧ p2) ∨ p1)) → ((p2 → p4) ∧ p3)) ∨ (((((p4 ∨ p1) → False) ∨ p2) ∨ (p2 ∨ False)) ∧ False)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113166850887594862089381556011 : (((p5 → (((((p4 ∨ (False ∧ False)) → p3) ∨ (p3 → (p4 ∧ (p4 → (p1 → (p3 → (p5 ∧ p5))))))) ∨ p1) → p3)) → p4) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_949594922190799475616201736798 : (((((p2 ∨ p5) ∨ p3) ∧ (((p1 → p5) ∧ (((p3 ∨ (False ∨ p1)) → (False ∧ p3)) ∨ (p4 → True))) ∧ (True → (False ∧ (False ∧ False))))) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h11 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h12 := h7 h11
        -- We need to get the left conjuct of h12 based on <expert-advice>.
        let h13 := h12.left
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h16 := h7 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h3.left
      let h20 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h25 := h20 h24
        -- We need to get the left conjuct of h25 based on <expert-advice>.
        let h26 := h25.left
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h29 := h20 h28
        -- We need to get the left conjuct of h29 based on <expert-advice>.
        let h30 := h29.left
        -- False on the left can always be used.
        apply False.elim h30
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h3.left
    let h33 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h34 := h32.left
    let h35 := h32.right
    -- Disjunctions on the left can always be decomposed.
    cases h35
    case inl h36 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h37 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h38 := h33 h37
      -- We need to get the left conjuct of h38 based on <expert-advice>.
      let h39 := h38.left
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
      have h41 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h33, we can now drive its conclusion.
      let h42 := h33 h41
      -- We need to get the left conjuct of h42 based on <expert-advice>.
      let h43 := h42.left
      -- False on the left can always be used.
      apply False.elim h43
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355653421590110903300238453220 : (p5 → (((p1 ∨ (p2 ∧ (((((p4 ∨ (p3 → p2)) ∨ p4) ∧ (p5 ∨ (p1 ∧ p4))) ∧ (p4 ∧ (p5 ∨ p4))) ∨ p4))) ∧ p2) → (p1 ∨ p5))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h16 =>
            -- Conjunctions on the left can always be decomposed.
            let h17 := h11.left
            let h18 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Conjunctions on the left can always be decomposed.
            let h24 := h11.left
            let h25 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h25
            case inl h26 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
            case inr h27 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h22
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h11.left
            let h31 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h31
            case inl h32 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
            case inr h33 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h1
          case inr h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- Conjunctions on the left can always be decomposed.
            let h37 := h11.left
            let h38 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h38
            case inl h39 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h35
            case inr h40 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h35
      case inr h41 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h11.left
          let h44 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h44
          case inl h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
          case inr h46 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h1
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h47.left
          let h49 := h47.right
          -- Conjunctions on the left can always be decomposed.
          let h50 := h11.left
          let h51 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h48
          case inr h53 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h48
    case inr h54 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47786337333062436926872035681 : (((((p3 ∧ ((p3 → False) → (((True ∧ p5) ∧ (p5 → (p2 → (p2 ∧ p3)))) ∨ (True ∨ (p1 ∧ False))))) ∧ True) → p2) → (True ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729965423700255963822292770107 : (((((p5 ∧ False) → p4) → ((((False → (False ∧ p1)) → ((False → (p1 ∧ True)) → (p1 → False))) → ((False → p1) → p3)) ∨ (True ∨ True))) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_118272053829837518653531343113 : ((p1 ∨ (((p2 ∨ p4) ∧ (False → (p3 → p1))) → (((p3 ∨ True) ∨ p3) ∧ (p4 ∧ ((((True → True) ∧ p5) → p3) → True))))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174141503155292825729116588131 : ((((((p3 ∧ (True ∨ (p3 → p4))) ∧ (True ∧ p2)) ∨ False) → p1) ∨ (False ∨ p2)) → (p4 ∨ (p2 ∨ (((False ∨ True) ∨ (True → p2)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909233245794438792906765872604 : (((((((p2 → p4) ∨ p3) ∧ p3) ∧ (p3 → (p4 ∧ ((p2 → ((p3 ∨ p1) ∨ False)) ∧ p1)))) ∧ ((True ∧ p1) → ((p3 → p2) ∧ p1))) → p2) ∧ True) := by
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
  cases h6
  case inl h8 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : (True ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h17 := h15 h16
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h20 := h5 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h23 : (True ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h22
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h24 := h3 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- One of the premise coincides with the conclusion.
    exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233600135303247395264060362636 : ((p2 ∨ (False ∧ p3)) → (((p4 ∨ ((p1 ∨ True) → p3)) → ((p4 ∨ p3) ∨ p1)) ∨ ((p1 ∧ (((p1 ∨ p1) → p4) ∧ p2)) ∧ (p5 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p1 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h7 := h5 h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156902846510844363268823098545 : ((((p3 → (p4 ∨ (((p4 ∧ False) ∨ (p5 ∨ (p5 → (p4 → False)))) ∨ (True ∧ False)))) ∨ p2) ∨ p3) ∨ (p3 ∨ ((p5 ∧ (p1 ∧ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310199698180923307272790944911 : (p2 ∨ (((((p1 ∨ (True ∧ (p1 ∨ (p2 ∧ p5)))) ∨ p1) → p2) ∧ p3) ∨ (False → (True ∧ (((p3 ∨ (True ∧ p4)) ∨ (False → p3)) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134946201894283438269992503171 : ((((False ∨ (((((False ∨ (p3 ∨ p2)) → (p3 ∨ p4)) → True) → (p5 ∨ p5)) → p5)) → (p4 ∧ p1)) ∧ (True ∨ p2)) ∨ ((p4 ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43909147995512011398202800042 : (((((((((((p3 ∨ p3) ∧ p1) ∧ (True ∨ p1)) ∨ (((True ∧ False) ∧ p1) ∧ p2)) ∨ p5) ∧ p1) ∨ p5) ∨ True) ∨ (p2 ∨ True)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244101803349695694131845945829 : ((True ∧ p3) ∨ ((True → p1) ∨ (((False ∨ p4) → (((True ∨ p3) ∨ p1) → ((p2 → False) ∨ (((p1 → (p3 → p2)) → False) ∨ True)))) ∧ True))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252315743365403533238814707269 : ((p4 → p5) ∨ (p1 → ((p5 → (p4 ∨ False)) ∨ ((((p1 ∧ (p3 ∨ p4)) ∧ p5) ∨ (((p5 ∧ p5) ∧ True) ∧ (False ∧ p5))) → (p2 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h12.left
    let h18 := h12.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62279905633489627915932974517 : ((p3 ∧ (((p2 → (True ∧ ((False ∨ (p1 ∨ p5)) ∨ p4))) ∨ (((p3 ∧ ((p2 → (False ∨ p2)) → p1)) → p3) ∨ (True ∨ p3))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191356797417380027143700972948 : (((p3 ∨ p3) ∨ ((True ∧ (p5 ∨ p1)) → (p4 ∧ p5))) ∨ (((((((False ∨ p2) ∨ p3) → (p4 → True)) ∨ p3) ∧ (True ∧ p3)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58320085536930200407242482151 : (((False ∨ True) ∧ (p4 ∨ ((False → p1) ∧ ((p3 ∨ ((p2 ∧ ((False ∧ True) ∨ (False → (True → (p3 ∨ (p3 ∨ p5)))))) ∨ False)) ∨ True)))) ∨ p4) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336215733818031432193613331948 : (p1 → (((True → (p4 ∨ ((p1 ∧ (((p4 → p4) ∧ True) ∧ ((((p2 → p5) ∧ p5) ∨ p1) ∨ (p5 ∧ p2)))) ∧ p5))) → (p3 ∧ p1)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183873926181346872291384820365 : (((((p2 ∧ p5) ∨ p1) ∧ (((p4 → p3) ∨ p2) ∧ p5)) ∧ p2) ∨ (False → (p3 → (((p2 ∧ (p5 → ((p5 ∨ p3) → True))) ∨ p1) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337857188069915186235057324615 : (p1 → ((((p1 ∧ ((p3 → (False ∨ True)) ∧ (p4 → p2))) ∨ p3) ∧ (False ∧ p2)) ∨ ((False ∨ ((p4 ∨ p1) ∨ p2)) ∧ ((p4 ∧ p3) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75497344660787427435591700758 : (((((p5 ∨ (((p4 ∨ ((p2 → p5) ∨ p4)) ∨ p1) ∧ p4)) ∨ ((True → (((p1 ∧ True) ∧ (p2 ∨ p4)) ∨ p5)) → True)) ∧ True) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (((p4 ∨ ((p2 → p5) ∨ p4)) ∨ p1) ∧ p4)) ∨ ((True → (((p1 ∧ True) ∧ (p2 ∨ p4)) ∨ p5)) → True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38644467512204352372257256293 : ((((((((p3 → p2) ∧ p5) ∨ p5) → p2) ∨ p3) → ((p2 ∧ (p1 ∨ ((p4 → p4) ∨ p3))) ∨ ((p2 ∨ (p3 → p3)) ∨ p2))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38060454263496582983887855705 : (((((((False ∨ (p2 ∨ p3)) → (p5 ∧ ((True ∨ (p1 → False)) → p5))) → p4) → (((p2 → p4) ∨ p1) ∨ p2)) → (p3 ∧ p4)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324711606834771118605896346415 : (p5 ∨ (((p2 ∧ p4) ∨ p4) → ((((False ∨ (((p5 ∧ ((p4 ∧ p2) ∧ (p5 ∧ True))) ∨ (p2 ∧ p3)) ∨ True)) ∧ False) ∨ (False → p5)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65598407800725310635514575997 : ((p4 ∨ (((True ∨ (p3 → (((p1 ∧ (p5 ∨ (False ∨ (p1 → p1)))) → p4) → (p5 ∧ p2)))) → (((p3 ∧ p1) → p2) ∧ p1)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158396342645596567122938659838 : (((p4 → p1) ∧ (((p1 ∧ (p2 ∧ (False → p1))) → False) ∨ (p1 ∨ (((p4 ∧ p3) ∧ p5) ∧ True)))) ∨ ((p2 → True) ∧ ((True ∨ False) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60198100747966014069620668543 : (((p5 ∨ p4) → (p3 ∨ ((((p5 → p2) ∧ (((p1 ∧ p4) → False) ∧ p2)) ∨ ((p2 ∧ p5) ∨ (((p3 ∨ p2) ∨ True) ∧ p3))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247454535458587082610180740336 : ((False ∨ p2) ∨ (p5 ∨ (((((p3 ∨ p1) ∨ p2) → (p2 → ((((p4 ∧ p2) ∨ (p2 ∨ (p5 → (p4 ∧ p2)))) ∨ False) ∨ p4))) ∧ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657369633005516822506922263184 : (((((p5 ∨ p3) ∧ (p5 ∧ (p4 ∧ ((((p5 → p4) ∨ ((p3 ∧ p4) → p1)) ∧ (p2 → (False ∨ (p4 ∨ p4)))) ∧ p2)))) ∨ (False ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114314520561313881743286111078 : ((((p4 ∧ (p3 ∧ (p4 ∨ p4))) ∨ ((True ∨ (((p2 ∧ p1) ∨ p5) → False)) ∧ (p1 → True))) ∧ (p4 ∧ ((p4 ∧ p1) ∨ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300399014968134515179219363824 : (False ∨ (((p4 → p1) → ((p1 → ((p1 ∧ p4) ∧ (p4 ∧ p3))) ∨ (True ∨ ((p5 → (False → p2)) ∨ (p1 ∧ p4))))) ∨ ((False ∧ p3) ∧ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227481065945176807503155374719 : ((True ∧ (p4 ∧ p2)) ∨ (((p4 → (False ∧ ((p5 ∧ ((((p2 ∧ (p1 → p2)) ∨ p2) ∨ p1) → p3)) ∨ ((p3 → p2) ∧ p5)))) ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206137472250993630732317833382 : ((p4 ∧ (p1 ∨ ((p2 ∨ False) ∨ p5))) ∨ (True ∨ (((True ∨ (((p3 ∨ ((True ∨ (p4 ∧ p5)) ∨ (p1 → p2))) → True) ∧ p2)) → True) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4440959563505111428551591895 : (p1 → (p5 → ((((((False ∨ (p1 → (((p2 ∧ p2) ∧ ((p3 → False) ∨ (p3 ∧ p3))) ∨ p1))) ∨ p5) ∨ True) → p3) → p3) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ (p1 → (((p2 ∧ p2) ∧ ((p3 → False) ∨ (p3 ∧ p3))) ∨ p1))) ∨ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301879801060933026992810205891 : (False ∨ ((p4 → p5) ∨ (True ∧ ((((p1 ∨ (p4 ∧ ((p1 → True) ∧ (True → (p3 → True))))) ∧ p3) → (p5 ∨ p1)) ∨ (p3 ∨ (True ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184236099085958226301629389311 : (((((((p1 → p4) ∨ False) → (p1 → p5)) ∨ p3) → p1) → False) ∨ ((p1 ∨ (p4 → (p5 → p5))) ∨ ((p5 ∨ ((p4 ∨ p5) ∨ p4)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322257980185523593117874923655 : (p5 ∨ (((((p2 → (p4 ∨ False)) ∨ True) ∧ (((p1 ∨ p2) → (p2 → p3)) ∧ ((((p1 ∧ p2) ∨ (p1 ∨ True)) ∨ False) → p5))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42017936555953441163236816058 : ((((True ∧ p1) ∨ ((p5 ∧ p5) ∨ (p3 ∧ ((p2 ∧ p3) ∧ ((((True → (p4 ∨ p1)) ∨ p1) ∧ p5) → (p3 → (p3 ∧ p2))))))) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259944731387182933472003794464 : ((p1 → p5) → ((((p1 ∨ p2) → False) ∨ (p5 ∧ p4)) → ((p5 ∨ (p3 ∨ (p5 ∨ (p3 → p3)))) ∨ (((p3 ∧ p2) ∨ True) ∧ (False ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613058585339687035309721464133 : (((((((((p2 → (p5 ∧ p2)) ∨ p2) ∧ True) ∧ (((p4 → (False → p2)) ∧ ((p2 ∨ p4) ∨ p1)) ∧ p1)) ∨ p5) → (p2 ∧ p3)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354704718230231232726344640578 : (p5 → (((((p3 ∧ p5) → False) → (((((p3 → (p2 → False)) ∨ p5) → p2) ∧ (((p3 ∧ True) ∧ p5) → p5)) → False)) → (p4 → p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63382657212674805504529094694 : ((p5 ∧ (False ∨ (((((((((p3 ∨ p5) → ((False → p1) ∧ p4)) ∧ p3) → p1) ∧ (True ∨ False)) → p2) ∧ (p3 ∨ p2)) ∧ True) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60609786502616738823129573860 : ((True ∧ ((((p3 ∧ p4) ∨ ((p5 → p4) ∨ ((False ∧ ((p2 ∨ (p5 ∧ ((p5 → p3) ∨ p5))) ∧ p1)) ∨ p5))) ∧ True) ∨ (True ∧ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225745609452869149069880292423 : (((p4 → p3) ∧ p4) ∨ ((p4 ∨ p1) → ((False ∨ ((False ∧ p3) ∨ ((True ∧ p2) ∨ ((True ∧ p1) ∨ (p4 ∨ (False → p4)))))) ∨ (p1 → p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_874858005685972158518303256607 : ((((((((False ∧ False) ∨ ((p1 → p5) ∧ (((True ∨ (p3 → (p4 ∨ (False ∧ p3)))) ∧ True) ∨ p1))) → p1) ∧ p5) ∨ False) ∧ (p1 → False)) → p3) ∧ True) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∧ False) ∨ ((p1 → p5) ∧ (((True ∨ (p3 → (p4 ∨ (False ∧ p3)))) ∧ True) ∨ p1))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h7
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48570074472126086165144324977 : (((((p4 → p5) ∨ (((p2 → (p2 ∨ (p3 → (True ∧ (p1 → (p5 ∧ p4)))))) → (p1 ∨ p1)) → p5)) → p4) ∧ (True ∨ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350287309614897051379361095069 : (p4 → ((False ∨ (((p5 ∨ (p2 ∨ ((((p1 ∧ (p3 ∨ p4)) ∨ p2) ∧ (True ∨ (p4 → p2))) ∨ (False ∧ (p1 → True))))) → p1) ∨ True)) ∨ p2)) := by
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
theorem thm_5_vars_45456277847422327461359266847 : (((True ∨ (p3 ∨ ((p5 ∨ ((p5 → p2) → ((((p1 ∧ p5) ∨ True) ∨ (p3 ∨ (False ∨ ((False → p2) → p4)))) ∧ p4))) ∧ p4))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345594527725841106920119588708 : (p3 → (((p2 → True) ∧ (p5 ∧ (True ∧ ((p5 ∧ ((p5 → p1) ∨ (((p4 ∧ ((p5 ∨ p3) → False)) ∧ True) ∨ (p3 ∧ p2)))) ∧ False)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133561277088199745964109214156 : (((((p2 ∨ ((((p5 ∨ True) → p4) ∨ p2) ∧ (p2 ∨ (((p1 → p4) ∨ p4) ∧ (p3 ∨ p5))))) ∨ p5) ∨ True) ∧ p2) ∨ ((p2 → p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114013813737356207725715289290 : (((((((False ∧ p4) ∧ (False ∨ (p2 ∧ (p2 → p4)))) ∨ ((True → (False → p5)) → p3)) ∧ True) ∨ p4) ∨ ((p3 ∧ False) ∨ p1)) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246524672777779790870349030872 : ((p5 ∧ p1) ∨ (((True ∨ p2) ∧ (False ∨ False)) ∨ ((False ∨ (p5 → False)) → ((((p3 → p2) → ((False ∨ p2) ∧ (p2 ∧ p2))) ∨ True) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200045927090605249995112558523 : (((p2 ∨ ((False ∧ p5) → p4)) → (p5 ∧ False)) → (((((p1 → (p3 ∨ False)) ∨ False) ∧ False) ∨ p3) ∧ ((False ∧ ((p2 → False) ∧ p1)) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((False ∧ p5) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p2 ∨ ((False ∧ p5) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h8
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h14
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : (p2 ∨ ((False ∧ p5) → p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (p2 ∨ ((False ∧ p5) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h18
  -- We need to get the right conjuct of h22 based on <expert-advice>.
  let h23 := h22.right
  -- False on the left can always be used.
  apply False.elim h23
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h24 : (p2 ∨ ((False ∧ p5) → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h28 := h1 h24
  -- We need to get the right conjuct of h28 based on <expert-advice>.
  let h29 := h28.right
  -- False on the left can always be used.
  apply False.elim h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315277691214051220865004721710 : (p3 ∨ (((True ∨ (p2 ∧ p4)) ∧ p4) → (((((((p3 → p3) → p3) ∨ ((p2 → (p5 → (False → p5))) → p3)) ∨ p2) → p3) → p5) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137767291055540292648872124679 : ((p2 ∨ (((False ∨ (p4 → ((p5 → (True → (False ∨ (p2 ∨ p5)))) ∧ (True ∧ p1)))) ∧ p4) ∨ (False → (False → p2)))) ∨ ((p3 ∨ p2) ∧ False)) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60449021987053157324617450413 : (((p5 → False) → (((p5 ∨ p1) ∧ (True ∨ ((p1 ∧ True) ∧ (p1 ∧ p4)))) ∧ (((((p4 ∧ (p5 ∨ True)) → False) → p2) ∨ p2) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57886282230864549726016196024 : (((p2 ∨ (p5 ∨ p5)) → ((p2 ∨ p4) ∨ ((((p1 ∨ False) → (((p1 → False) ∨ (p3 ∧ (p2 ∨ p5))) → (p5 ∨ False))) → p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646405597127279459871123384858 : ((((p1 → (((((p2 → False) ∧ ((False ∧ ((p5 ∧ p2) → True)) ∧ (p1 ∧ (p2 ∧ p3)))) ∧ (p4 ∨ p4)) ∧ (False → p3)) ∧ p2)) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118146333023936338815811304678 : ((False ∨ ((p2 ∧ (((p3 ∧ (p4 ∧ p1)) ∨ p3) ∧ (True ∨ p1))) ∧ (p2 → (True → ((p5 ∧ (p1 ∧ p3)) → (True → p1)))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201264164072023710506225766937 : ((p3 → ((p2 → True) ∨ (p2 ∧ (p2 ∨ False)))) → ((((p5 → (p5 → (p1 ∧ p2))) ∧ ((p1 ∨ False) ∧ p3)) ∨ (p4 ∧ (p1 ∨ False))) → p1)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325992008083803845594988179320 : (p5 ∨ (True → ((((((p1 ∧ p5) ∨ p4) → ((p1 ∧ (p5 ∨ (p2 ∧ p3))) ∧ True)) ∧ p3) ∨ (True ∧ (False ∧ p5))) ∨ ((False → p2) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85963834956993648392329078091 : (((((((False ∧ p4) → p3) ∨ p3) → False) ∧ (p4 ∧ p1)) ∧ ((p1 → p1) ∨ ((True ∧ (p5 ∨ ((p4 ∧ p3) ∨ p5))) ∨ (p3 ∧ p2)))) → p2) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h8 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h9 : (((False ∧ p4) → p3) ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h9
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
      cases h17
      case inl h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : (((False ∧ p4) → p3) ∨ p3) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- False on the left can always be used.
          apply False.elim h21
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h19
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h28 : (((False ∧ p4) → p3) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h29
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- False on the left can always be used.
            apply False.elim h30
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h32 := h4 h28
          -- False on the left can always be used.
          apply False.elim h32
        case inr h33 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h34 : (((False ∧ p4) → p3) ∨ p3) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h35
            -- Conjunctions on the left can always be decomposed.
            let h36 := h35.left
            let h37 := h35.right
            -- False on the left can always be used.
            apply False.elim h36
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h38 := h4 h34
          -- False on the left can always be used.
          apply False.elim h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- One of the premise coincides with the conclusion.
      exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178551416615956647130192702710 : ((((p2 ∨ (p2 ∧ (p1 → p4))) ∧ p3) ∧ ((p1 → (False ∧ p3)) ∨ False)) ∨ (p1 ∨ (((p4 ∧ p3) ∧ ((p2 → p1) ∧ p4)) → (p2 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197113800877724224277623922397 : (((False ∨ (p1 ∨ ((p3 ∧ p5) ∨ p1))) ∨ p3) ∨ ((((p1 ∧ False) ∧ (((p5 ∨ p2) ∧ (p3 → (True ∧ p4))) → (False ∨ p2))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57353949598393561760604224601 : (((p3 ∧ (True ∨ p3)) ∨ ((p2 ∨ (((p3 ∨ True) ∨ False) ∨ p3)) ∧ (p5 → (((p2 ∨ (p2 → p2)) → (p3 ∧ True)) ∨ (p1 → p1))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670546032958886013068465219887 : (((((p4 ∧ True) ∨ (True → (((p4 → ((p1 ∨ ((p4 ∧ (False → True)) ∨ p1)) ∨ False)) ∧ False) ∨ (p5 → False)))) ∨ (p3 → (False → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159264526438392189427423271908 : ((p4 → (((p4 ∧ (((False ∧ (p4 ∨ (p3 ∧ (p5 ∧ True)))) ∧ False) ∧ (True → False))) ∨ p2) ∧ p2)) ∨ ((p5 ∧ ((True ∨ True) ∧ p1)) → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352780237307537418736481783311 : (p4 → ((True ∨ p1) → (((p2 ∧ ((p4 → ((p4 ∧ (p5 ∨ (p5 → (p5 → p1)))) ∨ p1)) → (True ∧ p3))) ∨ (p5 → (p5 ∨ p2))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135545835518088605567926893893 : ((((p5 → (p5 ∧ (False → True))) → ((((p5 → False) → p1) ∧ True) ∧ (p3 ∧ p3))) ∧ ((p4 → p4) ∨ (p1 → p4))) ∨ ((p2 ∧ False) → p2)) := by
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
theorem thm_5_vars_308563910399613412319794948475 : (p2 ∨ ((((p1 ∧ False) ∨ (p5 ∧ (p3 → False))) ∨ ((True ∧ ((p1 ∨ ((p5 ∧ (p3 ∧ p4)) ∧ p1)) → p1)) ∨ (p1 ∨ (p4 → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134406606818477084042620716486 : (((p1 → (((True ∨ ((p3 → (((p2 → p3) → False) ∨ p5)) ∧ ((p3 → True) ∨ False))) → p5) ∨ (p3 → True))) ∨ p3) ∨ (p5 → (p4 ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608784548091660713892458291806 : (((((((p2 → p1) ∧ (p1 → (p5 → (((p4 ∧ ((p4 ∨ True) ∨ True)) ∧ p4) → (p2 ∧ p2))))) ∨ (True ∨ (False → p2))) ∨ p5) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156951175138114936781728044417 : ((((((((p2 ∨ False) ∧ ((p2 ∧ p5) ∧ p2)) ∨ False) ∨ p5) ∧ p2) ∧ ((p5 ∨ p3) → False)) ∨ p4) ∨ (False → (((p5 ∨ p2) ∧ p3) → p2))) := by
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252993509106832892144768514842 : ((True ∧ p3) → ((((((p5 → p5) ∧ (p4 → p2)) ∨ (((p5 ∨ (True ∨ True)) ∨ (True ∨ True)) → (p3 ∧ (p3 → False)))) ∨ True) ∨ True) ∨ p5)) := by
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
theorem thm_5_vars_323190524708418513909026068763 : (p5 ∨ ((((((((p3 ∧ ((p1 ∧ p4) → False)) → (p4 ∨ p1)) → False) → False) → (p2 ∧ (p2 ∨ p2))) → (p3 → p1)) → p5) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697087745858811828269344282295 : ((((((p3 ∧ True) ∨ (p4 ∧ p3)) ∧ (p5 ∧ ((p4 → p2) → p4))) ∧ (p2 ∨ (((True ∧ (p4 ∨ p2)) ∨ p1) → ((p4 → p3) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134919478039740338924663365686 : (((((p5 ∨ False) ∨ (p4 → ((p2 ∧ ((p3 ∨ p2) ∧ (((True ∨ p1) → True) ∨ True))) ∨ True))) ∨ p3) ∧ (p3 ∨ True)) ∨ ((False ∧ True) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716652903799231894981306973173 : (((((True ∨ p3) → (p1 → p3)) ∧ ((p4 ∨ False) → ((True ∧ ((((p3 → p5) → True) → ((False ∨ (True ∧ p5)) ∧ True)) → p1)) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38838884373714236156190681367 : (((((p2 → p2) ∧ p4) ∧ (p2 ∧ (((p2 → ((p5 ∨ p2) ∧ ((p3 → ((p1 ∧ p4) → False)) ∨ (p5 ∨ p3)))) → p3) ∨ p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682830485301987579406163736989 : (((((p3 ∨ (p2 → p3)) ∨ (True → (p1 → ((((p3 → False) ∨ (p1 ∧ False)) ∨ False) ∨ p5)))) ∧ ((True → p1) ∧ ((p1 ∨ True) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647173633478587536551413725745 : ((((p3 → (True ∨ ((((((p2 ∨ False) → p4) ∨ (((p2 → (True → (p2 ∨ p5))) ∧ (p5 → p4)) ∨ p1)) ∨ p1) ∧ p4) ∨ False))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218776713574027671246988623241 : ((p1 ∧ ((True ∧ True) → p2)) → (((((True ∧ (p5 ∧ True)) ∧ ((p2 ∧ (p5 ∧ False)) ∨ (False ∧ p4))) ∨ True) ∨ (p5 ∧ p5)) ∨ (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322453226575025307625212223693 : (p5 ∨ ((((p3 ∨ p2) ∨ p1) ∧ ((p3 ∧ p5) ∧ ((((p5 ∧ (p1 ∨ False)) → ((True ∧ (False ∨ p1)) ∨ (p4 → p3))) → True) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356255200272270925726419217924 : (p5 → (((((p1 ∨ ((p1 ∨ (p4 ∧ False)) ∨ True)) → True) → (p5 ∧ p4)) ∧ (False → p2)) ∨ ((p5 ∨ p1) ∨ ((p5 ∨ p1) → (p1 ∧ p3))))) := by
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
theorem thm_5_vars_47448629468556290785553802654 : (((p3 ∧ (p3 ∨ (((p5 → p5) ∧ (((p3 ∧ (False ∨ p1)) → p2) ∨ p5)) → ((p5 ∨ (p1 → (True → p3))) ∨ True)))) ∨ (p2 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252679866802182226186322017784 : ((p5 → p4) ∨ (p1 → (((p5 ∨ ((((False ∧ False) ∨ p3) ∧ ((p2 ∨ ((p4 → (p4 ∧ p2)) → p1)) ∨ False)) ∨ False)) ∧ p3) ∨ (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



