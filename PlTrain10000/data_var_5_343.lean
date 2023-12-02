variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251356644372348922936181555448 : ((p2 → p4) ∨ ((((True ∨ True) ∧ False) ∨ (p2 ∨ ((((((p4 → p3) ∧ p2) → p1) ∧ ((p2 ∨ (p5 ∧ p2)) → p5)) ∨ p4) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258537151182029814348832695624 : ((p5 ∨ p3) → ((((((True ∧ False) ∨ (((((p3 ∨ p1) ∨ True) ∨ True) ∨ p1) ∨ (p2 ∧ False))) ∧ p4) ∨ p5) ∨ p3) → ((True → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
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
                cases h15
                case inl h16 =>
                  -- Disjunctions on the left can always be decomposed.
                  cases h1
                  case inl h17 =>
                    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                    have h18 : True := by
                      -- True on the right can always be proven directly.
                      apply True.intro
                    -- We have shown the premise of h3, we can now drive its conclusion.
                    let h19 := h3 h18
                    -- One of the premise coincides with the conclusion.
                    exact h19
                  case inr h20 =>
                    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                    have h21 : True := by
                      -- True on the right can always be proven directly.
                      apply True.intro
                    -- We have shown the premise of h3, we can now drive its conclusion.
                    let h22 := h3 h21
                    -- One of the premise coincides with the conclusion.
                    exact h22
                case inr h23 =>
                  -- Disjunctions on the left can always be decomposed.
                  cases h1
                  case inl h24 =>
                    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                    have h25 : True := by
                      -- True on the right can always be proven directly.
                      apply True.intro
                    -- We have shown the premise of h3, we can now drive its conclusion.
                    let h26 := h3 h25
                    -- One of the premise coincides with the conclusion.
                    exact h26
                  case inr h27 =>
                    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                    have h28 : True := by
                      -- True on the right can always be proven directly.
                      apply True.intro
                    -- We have shown the premise of h3, we can now drive its conclusion.
                    let h29 := h3 h28
                    -- One of the premise coincides with the conclusion.
                    exact h29
              case inr h30 =>
                -- Disjunctions on the left can always be decomposed.
                cases h1
                case inl h31 =>
                  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                  have h32 : True := by
                    -- True on the right can always be proven directly.
                    apply True.intro
                  -- We have shown the premise of h3, we can now drive its conclusion.
                  let h33 := h3 h32
                  -- One of the premise coincides with the conclusion.
                  exact h33
                case inr h34 =>
                  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                  have h35 : True := by
                    -- True on the right can always be proven directly.
                    apply True.intro
                  -- We have shown the premise of h3, we can now drive its conclusion.
                  let h36 := h3 h35
                  -- One of the premise coincides with the conclusion.
                  exact h36
            case inr h37 =>
              -- Disjunctions on the left can always be decomposed.
              cases h1
              case inl h38 =>
                -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                have h39 : True := by
                  -- True on the right can always be proven directly.
                  apply True.intro
                -- We have shown the premise of h3, we can now drive its conclusion.
                let h40 := h3 h39
                -- One of the premise coincides with the conclusion.
                exact h40
              case inr h41 =>
                -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
                have h42 : True := by
                  -- True on the right can always be proven directly.
                  apply True.intro
                -- We have shown the premise of h3, we can now drive its conclusion.
                let h43 := h3 h42
                -- One of the premise coincides with the conclusion.
                exact h43
          case inr h44 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h45 =>
              -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
              have h46 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h3, we can now drive its conclusion.
              let h47 := h3 h46
              -- One of the premise coincides with the conclusion.
              exact h47
            case inr h48 =>
              -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
              have h49 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h3, we can now drive its conclusion.
              let h50 := h3 h49
              -- One of the premise coincides with the conclusion.
              exact h50
        case inr h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- False on the left can always be used.
          apply False.elim h53
    case inr h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h55 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h56 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h57 := h3 h56
        -- One of the premise coincides with the conclusion.
        exact h57
      case inr h58 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h59 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h60 := h3 h59
        -- One of the premise coincides with the conclusion.
        exact h60
  case inr h61 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h62 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h63 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h64 := h3 h63
      -- One of the premise coincides with the conclusion.
      exact h64
    case inr h65 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h66 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h67 := h3 h66
      -- One of the premise coincides with the conclusion.
      exact h67



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186649713211056391684478275121 : ((((p2 ∧ ((p5 ∨ p3) → False)) ∧ True) ∧ ((p4 ∨ p2) ∨ p3)) → ((((((p1 → (p4 ∧ True)) → False) ∧ p3) ∧ p4) → p1) ∧ (p2 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : (p5 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h16 := h12 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h18 : (p5 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h19 := h12 h18
      -- False on the left can always be used.
      apply False.elim h19
  case inr h20 =>
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h21 : (p5 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h22 := h12 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h25 := h23.left
  let h26 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h30 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h31 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h31
  case inr h32 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190321326575740128461454334776 : (((((p2 ∧ p3) ∧ (p1 ∧ p4)) ∨ (p1 ∧ p4)) ∨ p4) ∨ (False ∨ (((False ∨ (((False ∧ (True ∨ p5)) ∨ (True ∧ p2)) ∨ p5)) ∨ p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118691668585458617497528151002 : ((p5 ∨ ((((((False → True) → ((p3 ∨ p2) ∧ (True ∧ (p2 ∨ p3)))) → ((False → (p5 → p3)) → p5)) ∨ p5) → p5) ∨ p2)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57358008333464000422441503199 : (((p3 ∧ (False → p1)) ∨ ((p3 ∧ p1) ∨ ((((p4 ∨ (p1 → False)) → (p1 → ((p3 ∧ p5) ∨ (True ∧ (True ∨ p3))))) ∨ False) ∨ p5))) ∨ p2) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253011429723605828098202799502 : ((True ∧ p3) → ((p3 ∨ ((False ∧ ((p2 ∧ (((True → False) ∧ True) ∨ p5)) ∨ ((True ∧ True) → p1))) → (p4 ∨ p1))) → ((True → p4) → p4))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216390484696318917349402026892 : ((p3 → (p2 ∨ (p1 ∨ p2))) ∨ (((p3 ∨ ((((p2 ∨ ((p2 → p5) ∧ p3)) ∧ True) → (p5 ∨ (p5 ∧ p2))) → (p5 → p1))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221102735470051469890526778434 : (((p5 ∧ p4) ∨ True) ∧ (p4 → ((((False ∧ (p2 ∨ ((p2 → (p1 ∧ p1)) ∧ p3))) ∧ ((p4 → p2) ∧ False)) ∨ (True ∨ p5)) ∨ (p1 ∧ p4)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136845518972913564299051503897 : (((p3 ∧ False) ∨ ((((True ∨ (p1 ∨ p4)) → p4) ∧ p3) → ((p4 ∨ p5) ∧ ((p5 ∧ (p5 ∧ p1)) ∨ (p3 ∧ True))))) ∨ ((p1 ∨ p1) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ (p1 ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596229896189555752958743986993 : ((((((p3 ∨ p2) ∧ (((p4 ∨ p5) ∨ p5) ∨ False)) ∧ (((p2 ∧ p2) ∨ ((((p1 ∨ p5) → p5) → (False ∨ p3)) ∧ p1)) → p4)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184332093310694191031149250324 : (((True ∧ ((p5 ∧ (p3 ∨ ((False ∧ p5) ∨ True))) → p4)) → p4) ∨ ((p2 ∨ ((p4 ∨ ((p5 → p4) ∧ p5)) → p4)) ∨ ((True ∨ False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204171474198165975167114396818 : ((((p3 ∧ (True ∨ True)) ∨ p4) ∧ p5) ∨ (p3 → ((p2 ∧ ((p5 ∨ p3) → p5)) → ((False ∨ ((False → (p1 → p1)) ∨ p1)) → (p5 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h2.left
      let h8 := h2.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : (p5 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h2.left
      let h13 := h2.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200072899908361150612152114047 : ((((p5 ∨ p2) ∧ p3) ∧ ((p2 ∧ True) ∧ p1)) → ((((p3 ∨ True) → False) ∨ p4) ∨ (True ∧ (True ∧ (((p3 ∨ True) ∨ (False → p5)) → p3))))) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
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
    -- Implications on the right can always be decomposed.
    intro h11
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
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
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60743975808945379241715783163 : ((True ∧ (((False ∨ p1) → False) ∨ (((p1 ∧ p2) ∨ (p1 ∧ (((p4 → (p1 ∧ p5)) ∨ (True → True)) ∨ p1))) → (False ∧ (p4 ∨ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62425033783653884611976169217 : ((p3 ∧ ((True ∧ ((p4 ∨ p5) ∨ p3)) ∧ ((((p5 → p1) ∨ (p3 ∨ p3)) ∧ ((True ∨ ((False ∧ (p4 → True)) → p2)) → False)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255591443532045019843946017866 : ((p5 ∧ p3) → (p4 ∨ (((p1 ∨ (((((p5 ∧ p5) → p5) → ((p2 ∧ (True ∨ (False ∨ p1))) ∧ p1)) ∨ (p4 → p4)) → p4)) ∨ p5) ∧ True))) := by
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
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358737992785236298173766981909 : (p5 → (p5 → ((p2 ∨ p5) → ((p3 ∨ (((((False ∨ p4) ∧ p4) → (p4 ∧ (p5 ∧ p4))) → p5) ∧ (p3 ∨ (p2 ∧ (p1 → p4))))) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89203853602620373767163193776 : ((((p5 → p5) → False) ∧ ((((((p5 → (p2 ∧ (p3 ∧ p3))) ∨ True) ∧ p4) ∨ p4) ∧ ((p3 → ((p1 → p2) → True)) → p2)) → False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → p5) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187824674925955286682818957262 : ((p4 → (False ∧ (p3 ∨ (True ∨ (p3 → (p5 ∨ (p3 ∨ p3))))))) → (p2 ∨ ((p5 → p3) ∨ (p5 → ((p2 ∧ (True ∨ p5)) ∨ (p2 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48464743559288806566410091162 : (((((False ∨ (p1 ∨ ((((p3 ∨ p5) → False) ∧ True) → (p5 ∧ ((p2 ∧ p1) ∧ (False → p3)))))) → p4) ∧ True) ∧ (p3 ∨ (p5 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791947296951282636907707999678 : (((True → ((p3 ∧ ((False ∨ (((p2 ∧ False) ∨ True) ∧ (((((p5 ∧ p5) ∧ (p4 ∨ True)) → p3) ∨ False) → False))) ∧ True)) ∨ (p3 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209212578990571742254917781757 : ((p4 ∨ (p2 ∨ ((False ∨ p4) ∨ p1))) → (((p2 ∧ p1) ∧ (p4 ∧ (p4 ∧ (True ∧ ((True ∧ p4) → ((p3 ∨ (p1 → p3)) → p1)))))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340940097464530307697157402772 : (p2 → (((((p1 ∨ p3) ∨ p1) ∨ p2) → ((p5 → ((((p5 ∧ (False ∧ p1)) ∧ p5) → p2) ∧ ((True ∨ p3) → False))) → (True → p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187355294940496132054331418736 : ((p3 ∧ (((p2 → p5) ∨ ((p4 ∧ p2) ∨ (True → p5))) ∧ p1)) → ((((p3 → p1) ∧ False) ∧ p2) ∨ ((False ∧ ((p1 → p1) ∧ p3)) → p1))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175431695194553316258867293219 : ((p1 → (((True ∧ p4) ∨ (((((False ∨ p1) ∧ p4) → p2) → p5) ∧ p2)) ∨ p1)) → ((p2 ∧ p3) → (((p2 → (p5 ∨ True)) ∨ p4) ∨ p3))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55821444432099672478237715098 : ((((p1 → True) → (p4 ∧ False)) ∧ ((p1 → (False ∨ p3)) ∧ ((p4 ∨ (p5 → ((p1 ∧ ((p2 → (p4 ∨ p4)) ∧ p5)) → p3))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61009956984566293428036384884 : ((False ∧ (((p3 → p1) ∧ (p4 → ((False ∧ (((p4 → (p2 ∧ ((p1 ∧ True) → (p1 → False)))) → p3) ∧ p1)) ∧ (False → p1)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597206231186836597486126492561 : (((((((p3 → True) ∨ p2) → False) ∧ ((p4 ∨ p3) → ((p1 → (p5 → ((p2 → p3) → ((p3 → (p2 ∧ p1)) ∨ p3)))) → False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597131435615213284745005031475 : (((((p3 → ((p3 → False) ∧ (p2 ∧ False))) → (p5 ∧ (p4 → (((True → ((p1 ∨ True) → (p1 ∨ (p2 → p5)))) ∧ p4) ∧ True)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256787018993035834064734997705 : ((p1 ∨ p2) → ((p5 ∨ ((p4 → p5) ∨ (p3 ∨ p4))) → (p2 ∨ (p3 → (((p2 ∨ p5) ∨ p4) ∨ ((p2 → (p4 → (p1 ∧ True))) ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h18
          -- Implications on the right can always be decomposed.
          intro h19
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h16
          -- True on the right can always be proven directly.
          apply True.intro
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h20 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h24 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190235062085307292720098391347 : (((((p5 ∧ (p1 → (p3 ∨ p3))) ∧ p4) ∧ False) ∨ p3) ∨ ((p5 ∨ ((p5 ∧ (((p4 ∨ False) ∧ False) → p2)) ∧ (p1 → p5))) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171325312210182430116902694795 : (((((p5 → (p3 ∨ p2)) ∨ (p5 ∧ (p3 ∧ ((p5 ∨ p5) → p1)))) ∨ p4) ∧ p2) ∨ (False → (((p1 → p5) → True) ∨ ((True ∧ p3) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183110741745747464852033765714 : (((p4 ∨ p2) → ((False → (p3 → p1)) ∨ (p2 → (p2 → p3)))) ∧ (p3 → ((p1 → (p4 ∨ (p5 → p3))) → ((p1 ∧ (p3 → False)) → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233829929842179007337417970319 : ((p4 ∨ (True ∧ p2)) → ((p1 → (((p4 ∨ False) ∧ True) ∧ p3)) → ((p1 ∧ (p5 ∧ p5)) ∨ (p2 → ((((p1 → p3) → True) ∨ p2) ∨ p3))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38416344504971465546921358546 : ((((((False ∧ p5) → False) ∧ ((p2 ∨ (((False ∧ p2) → True) ∧ p2)) ∨ p5)) ∧ (p5 ∨ (((True ∨ (p1 ∧ False)) ∨ True) ∨ p1))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113482525093863055744296608886 : ((((((False ∨ p1) ∧ p5) → (((p1 ∨ True) ∨ (True ∨ ((p3 ∨ True) ∧ False))) ∧ (False ∧ p1))) ∨ (p5 ∧ p5)) ∨ (p1 ∨ False)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646962937866486719890024015823 : ((((p3 → (((p4 ∨ ((p5 ∧ p2) → (False → p4))) ∧ (True ∨ (p3 ∨ (((False ∨ False) → (p5 ∨ (p5 → p4))) ∧ p3)))) ∧ False)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349989460151691409718170699773 : (p4 → ((((((True ∧ (False ∧ (p2 ∧ ((p3 → p4) ∨ p4)))) → ((p1 → p2) → (p5 ∧ False))) → p1) → ((p2 ∧ p2) ∨ p3)) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133663007182350474323637414412 : ((((p4 ∧ ((p1 ∧ ((p3 ∧ ((p5 ∨ (p3 → (p2 ∨ p5))) ∨ p4)) → p5)) ∧ (False → p5))) ∨ (p3 ∨ False)) ∧ p5) ∨ ((True → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66442578981463370586967319778 : ((True → (((((p4 ∨ (p1 ∧ p5)) ∨ (p5 ∨ (((False ∨ True) ∨ (p1 ∨ False)) ∧ (p2 → (True ∧ p1))))) ∧ p2) ∧ (p4 → p1)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41854256989618107601143792275 : (((((p5 ∧ True) ∧ False) ∨ (((p5 → ((p4 ∧ p1) → ((((False ∨ p2) → False) → ((p1 → p4) ∧ p2)) ∨ True))) ∨ p5) ∨ p5)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191796018923617115100449712517 : ((p2 ∨ ((((p3 ∨ p4) → p1) ∨ (p2 ∧ True)) ∨ p5)) ∨ ((p1 ∧ ((p2 ∨ (p4 ∧ p2)) ∧ ((p2 → (p3 → p2)) → p2))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641923335887283767754400526766 : (((((p3 → p1) → (p3 → (((p5 → (((True ∨ True) → ((p2 ∨ p2) → p5)) ∧ p3)) ∧ p1) ∧ ((True ∧ p4) ∨ (p1 → p2))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228893747815856873143073078343 : ((p4 ∨ (p3 ∧ p3)) ∨ ((True ∨ p2) → ((((p2 ∨ (False ∨ p1)) ∧ p4) ∨ ((False → True) ∨ (True ∨ ((False ∨ True) ∨ (p1 → p3))))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342162205840434881536271168673 : (p2 → (((((p5 ∧ p3) ∨ (False ∧ p4)) ∧ p4) ∧ ((p2 → False) → (p5 → ((True ∧ (p1 → True)) → p1)))) ∨ ((p2 → p1) ∨ (p2 ∨ False)))) := by
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
theorem thm_5_vars_312033269106067273233643751626 : (p2 ∨ (p4 ∨ (p5 ∨ ((p1 ∨ (p4 ∧ (False ∨ (((True ∧ (True ∨ p3)) ∧ p2) → p1)))) ∨ (((True ∨ ((p1 → True) ∨ p1)) ∧ p2) ∨ True))))) := by
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
theorem thm_5_vars_239588673869206941657540880084 : ((p3 ∨ True) ∧ (((p4 → ((p5 ∨ ((p5 ∧ (p2 ∨ ((p4 → p2) ∨ p2))) ∧ p4)) ∧ ((p2 → p1) ∨ p5))) ∨ True) ∨ ((p1 ∨ p5) → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344180224383846148389445538880 : (p2 → (p1 ∨ (((((((False → True) ∨ False) → (p3 ∧ (True ∧ ((p1 ∨ p4) ∨ p3)))) ∧ (p4 ∨ p1)) → False) ∧ p3) ∨ ((p5 → p5) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590983854323596450782240450590 : (((((p2 → (((True ∨ p3) ∧ p3) ∨ (((p3 ∨ p2) ∧ ((False ∧ (False ∨ (p3 ∨ (p2 → p4)))) → (False ∨ True))) → p5))) → p4) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173819083999524211687020497391 : (((p1 ∨ ((((False ∧ p4) ∧ p3) → ((p3 ∧ (p5 → p5)) ∨ p4)) ∨ p4)) ∨ p4) → (True ∧ ((((True → (True ∧ p5)) ∧ p2) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52168105010839478636258373754 : ((((((False ∧ p3) → ((p1 → True) ∨ True)) ∧ True) → ((p1 → True) ∧ (p3 ∨ p1))) → (((p5 ∧ False) ∨ ((p5 → False) → p1)) ∨ p3)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False ∧ p3) → ((p1 → True) ∨ True)) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357984623448783160771496491677 : (p5 → (False ∨ (((((p5 ∧ (p4 ∧ True)) ∨ (True ∧ (((((True ∧ p3) ∨ p3) → p4) ∧ True) → p3))) ∧ (p3 → False)) ∧ p1) ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698687965363113411767937016553 : (((((False ∧ p1) ∧ ((p2 → p1) ∧ (p5 ∨ ((p1 → p1) → p3)))) ∨ ((p5 ∨ (False ∧ (p1 → ((False ∨ p4) → False)))) ∨ (True → True))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114833065231857491078040241299 : (((p2 → ((p2 ∨ ((p3 ∧ True) → ((p1 ∨ (p2 ∨ p5)) ∨ False))) ∧ False)) ∧ (p3 → ((p2 → ((p1 → False) ∨ p1)) ∨ p5))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64069192881432852980300440939 : ((False ∨ ((((True → p3) ∧ ((((p2 → p3) ∨ p5) ∨ p1) ∨ True)) → ((p4 ∧ p2) ∨ True)) ∨ (p4 ∨ ((p2 ∧ p4) ∧ (p2 → p1))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
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
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199637496531703636844043247068 : ((((False ∨ (p3 ∧ p5)) ∨ (p3 → True)) → True) → (((((p2 → (p1 ∧ (p3 ∨ (True ∨ p4)))) ∨ (True ∧ (False → p5))) → p3) ∧ p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260065863468319198336947436127 : ((p2 → False) → ((False ∨ ((p3 → False) → (p1 ∨ p5))) ∨ ((p2 → (((p3 ∨ (p4 → False)) ∧ p5) → ((p1 → (p2 ∨ True)) ∧ p1))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h9 := h3.left
  let h10 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h16 := h1 h15
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135304585296992203502677040301 : ((((p3 ∨ ((True ∧ False) ∨ (p1 → (p5 ∧ ((True ∨ (p5 ∨ (p5 → p3))) → p3))))) ∨ p4) ∧ (p1 → (True ∨ p2))) ∨ (False ∨ (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749125948851033383529758953311 : ((((p5 → False) → (p4 → (p2 ∧ (p2 ∧ (((p2 ∨ ((p5 → p1) → (p1 → ((p1 ∨ (p1 ∧ p3)) → False)))) ∨ True) ∧ (p4 ∨ p1)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693179073256803926758693727545 : ((((True ∨ ((p4 ∧ p2) → (p1 → (p5 ∨ (p1 ∧ (p1 ∧ (p1 ∨ True))))))) ∧ (False ∧ (p4 ∨ (p2 → (((p1 ∧ p1) ∧ p4) ∨ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356165208763064535818289388298 : (p5 → ((False ∧ (((p4 → (((p5 → False) → p3) → ((True → (False ∧ False)) ∧ p5))) ∨ p5) ∨ False)) ∨ ((((p2 ∧ p3) → p5) → p5) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114848381937039185296074107170 : ((((p1 ∧ (p4 ∧ (p4 → ((p2 ∧ p2) ∧ ((p4 ∧ p4) ∧ p2))))) ∨ p2) ∨ ((p2 ∨ (((p4 ∧ p4) ∨ False) ∨ p4)) ∨ p1)) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300069613671005825333711805835 : (False ∨ (((False ∨ (((p1 ∧ p2) ∨ (p4 ∧ p4)) ∨ ((((((p2 ∧ p4) ∧ p4) → False) ∧ p1) ∧ p3) → (True ∨ p1)))) ∨ False) ∨ (p3 ∧ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711386353811248863666254725179 : ((((p2 ∨ ((p4 ∨ p4) ∨ (p2 ∨ True))) ∧ ((p4 → (p4 ∨ p3)) ∧ (p3 → (((True ∧ ((p4 → (False ∨ p4)) ∨ p4)) ∨ p4) ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213278370329062035536737428184 : ((((False → p1) → p2) ∧ p3) ∨ (p1 → (p3 → (((((False ∧ False) ∧ True) ∨ True) ∨ ((p4 ∧ p4) ∨ (True ∧ (p3 → (p3 → True))))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59057093253608562566711881871 : (((p4 ∧ p4) ∨ (p2 → ((p2 → p3) → (((True → True) → (p4 ∧ p5)) ∨ (((p2 → ((p5 ∨ p3) → p2)) ∨ (p5 ∧ p2)) ∨ p4))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56638001042535411773968901676 : ((((True ∨ False) ∧ p2) ∧ ((p5 ∨ ((False ∨ (p2 → (p3 ∧ ((True → ((p1 ∧ p4) ∧ True)) → (p2 → p4))))) ∧ p5)) → (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682072316843124684884715062916 : (((((p4 → ((p1 → ((((p1 → p2) ∨ p1) → p5) ∧ ((p2 ∧ False) ∧ False))) → p3)) ∨ p1) ∧ (True ∨ ((p5 → (p5 → p2)) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181428779338246577701202578621 : ((p3 ∨ (((((p2 → True) ∧ True) ∨ (True → p4)) → (p4 ∧ False)) ∧ p4)) → (p3 ∨ ((p1 → p4) → (((p3 → (False → p3)) → p4) ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (((p2 → True) ∧ True) ∨ (True → p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67838325472390405022953561752 : ((p2 → ((((p2 ∨ (((p1 → (((True → p2) ∧ (p2 → p5)) → (p3 ∧ p3))) ∧ False) → p4)) ∧ (p5 ∧ p3)) → p4) ∨ (p3 → p3))) ∨ p3) := by
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
theorem thm_5_vars_59755719907707466515997200650 : (((p1 ∧ p3) → (((((True → (True → ((((p3 ∨ (True → p5)) → True) ∧ (p2 → False)) ∨ p5))) ∨ False) ∧ (p3 → p3)) ∨ p4) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45950762133319806655047965999 : (((p5 → (((p5 → (((p5 → (p2 → ((p3 ∧ p4) → p4))) ∨ p2) → p2)) → (p3 → p4)) → ((p4 ∨ False) ∨ (p3 ∧ True)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318861704022636533838579203659 : (p4 ∨ (((p2 ∨ (((p1 ∨ (p5 → (True ∧ p3))) → p5) → (p3 → (p2 ∨ (p5 → ((p4 ∧ False) ∨ True)))))) → p4) ∨ (p3 → (False ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328977484562080098760544935804 : (True → (((p3 ∧ ((p4 ∧ False) ∨ False)) ∧ p4) ∨ (((False → (p1 ∨ (True ∧ p3))) ∨ p1) ∨ (p4 ∧ ((((False ∨ p5) ∨ p2) ∧ False) ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171435190352691679067366380304 : ((((True ∨ p3) → ((p3 ∨ (p4 → (True ∨ (True ∨ p2)))) ∨ (p5 → p3))) ∧ p5) ∨ ((((p2 → False) ∧ (False ∨ p5)) ∨ True) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129208626623588000489800353927 : ((((((((p5 → p3) ∧ p2) ∨ (p1 ∨ p3)) ∧ (p4 ∨ (p1 ∨ False))) ∧ p2) ∨ ((p2 → (False ∧ p1)) ∧ p1)) ∨ True) ∧ (False → (False → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200699758243443752747336837300 : ((p2 ∧ ((False ∨ (p3 ∨ True)) → (True ∧ False))) → (p5 ∧ ((((p1 → p3) ∧ (p3 ∧ False)) ∧ p5) ∧ ((p1 → True) ∧ (False ∧ (p4 → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
  have h15 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h14, we can now drive its conclusion.
  let h16 := h14 h15
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
  have h20 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h19, we can now drive its conclusion.
  let h21 := h19 h20
  -- We need to get the right conjuct of h21 based on <expert-advice>.
  let h22 := h21.right
  -- False on the left can always be used.
  apply False.elim h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h1.left
  let h24 := h1.right
  -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
  have h25 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h24, we can now drive its conclusion.
  let h26 := h24 h25
  -- We need to get the right conjuct of h26 based on <expert-advice>.
  let h27 := h26.right
  -- False on the left can always be used.
  apply False.elim h27
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h28
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h29 := h1.left
  let h30 := h1.right
  -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
  have h31 : (False ∨ (p3 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h30, we can now drive its conclusion.
  let h32 := h30 h31
  -- We need to get the right conjuct of h32 based on <expert-advice>.
  let h33 := h32.right
  -- False on the left can always be used.
  apply False.elim h33
  -- Implications on the right can always be decomposed.
  intro h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338118462048778891332228281682 : (p1 → (((((p1 ∧ False) ∨ (p3 ∧ p1)) ∧ p3) ∧ p5) ∨ ((p4 ∧ p4) → ((p3 → (((((p5 → p5) → p2) ∨ p5) ∧ p4) ∨ p3)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114001681702974478515930490701 : (((((False ∧ (p4 ∧ (p1 ∨ (((p4 ∧ False) ∨ (p2 → p1)) ∧ ((p5 ∨ p5) ∧ p2))))) ∧ p3) ∧ p1) ∨ (True → (p4 ∨ True))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51236026062740704734695762910 : (((((p1 → p2) ∨ p5) ∧ (p1 ∧ (((p5 ∧ p3) ∨ (True ∧ p5)) ∨ (p4 ∨ (p1 ∨ False))))) ∨ (((p5 ∨ (p2 ∨ False)) ∧ True) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615928645198158882867168370927 : (((((p3 → (p4 ∨ ((p2 ∨ p5) ∨ ((p3 → (p5 ∧ p3)) ∨ (p2 ∨ p3))))) ∨ ((p1 ∧ p1) ∧ (((p4 → p4) ∧ p3) ∨ True))) ∨ False) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207243365112621275930365768581 : ((((p1 ∧ (False ∧ p5)) ∨ True) ∨ True) → (p3 ∨ ((((p2 ∧ p5) ∨ p3) → (((p1 ∧ True) ∧ (p4 ∧ p2)) ∨ (p4 → (False → p3)))) ∨ False))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Implications on the right can always be decomposed.
      intro h27
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164991126071432045853422227623 : (((((((p4 → True) ∨ (p5 ∧ p3)) ∨ (p1 → p4)) → p4) → ((p3 → p5) ∨ p2)) → p4) ∨ ((((p1 ∨ p4) ∧ p5) ∧ False) → (False ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773969927474580951911613720253 : (((False ∨ (((True → ((((p2 → (p4 → ((p1 ∨ p2) ∨ p5))) ∧ p2) ∨ p2) → (((True ∨ p3) → p4) ∧ p3))) ∨ p1) ∧ (p4 ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302500144129274111822433040129 : (False ∨ (False ∨ ((p4 ∨ (((p4 ∧ p1) ∨ (((p4 → p3) ∨ ((((True ∨ p5) → ((p1 → True) ∨ p5)) ∨ p5) ∧ p5)) ∨ p5)) ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115800782648114036482119824336 : ((((p4 → (p3 → p4)) ∨ p2) ∧ (((((True ∨ p1) ∧ False) → ((True ∨ p4) ∨ ((p5 ∨ p4) → p1))) → p2) ∧ (p5 ∨ p2))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739669846761804997526995913644 : ((((p5 ∧ p5) ∨ (p1 ∧ (((p1 ∨ (((((p4 ∨ p2) ∨ p5) ∨ p2) ∧ ((True ∧ (p3 → True)) → (p3 ∨ p2))) → p3)) → False) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164802156017402243169382830188 : ((((p1 ∧ (p3 ∧ p2)) ∨ (((p2 → (p3 ∨ p1)) → p3) ∧ ((p1 → p4) ∧ p5))) ∨ True) ∨ ((p4 ∨ (p3 → p2)) ∨ (p2 → (p3 ∨ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193798361773553641659177059630 : ((p4 ∧ (p3 ∨ ((p2 ∧ (p1 ∨ p3)) ∧ (False → p2)))) → ((((True → (p4 → p3)) ∧ ((True ∧ p5) ∧ p3)) ∧ p5) ∨ (p4 ∨ (p5 ∧ p3)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64641498033691567347919205156 : ((p1 ∨ (p4 ∧ ((p2 ∧ (((p2 → p4) → ((p1 → p3) ∧ (p1 → True))) ∨ (((p3 ∨ p3) ∧ ((p3 ∧ p3) ∨ p5)) ∨ p3))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588402770667986719876980299345 : (((((((p5 ∧ p2) → False) ∨ (p3 → ((p5 ∧ ((p1 ∨ (p2 ∨ True)) ∧ p1)) ∨ (p5 ∧ (p5 → (p1 ∧ (p5 ∧ False))))))) ∨ True) ∧ True) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50584390181079769218767771173 : ((((p1 ∨ (p5 ∧ (False ∧ (p4 ∨ (False ∧ ((p2 → (p1 ∨ p3)) → ((p2 ∨ False) → p5))))))) → False) → ((p5 ∨ p3) → (p5 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306649754919599612102795027707 : (p1 ∨ (True ∧ (((False ∨ ((True ∧ p3) → p2)) ∧ (((p3 ∧ p1) ∧ True) → ((p3 ∧ (p5 ∨ p4)) ∨ (p5 ∨ p5)))) ∨ (p3 → (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164477407603689687985862545853 : (((((p2 ∨ p3) ∨ (p4 ∧ ((True ∧ (p4 → (p1 ∨ p5))) → (True ∧ p2)))) ∨ p3) ∧ p1) ∨ ((False ∧ p5) ∨ (((p3 ∨ True) ∨ p1) ∨ p5))) := by
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
theorem thm_5_vars_199102147612279571244610077336 : ((((p1 ∨ (p3 ∨ True)) ∧ (p2 ∨ p5)) ∧ p4) → (((((p3 ∧ p4) ∨ ((p2 → p5) → p2)) → p5) → (False ∧ (False → p2))) ∨ (True ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230559914951413344028699899861 : (((False → p5) ∧ p5) → (p1 ∨ ((p1 ∨ p4) ∨ (((p1 ∧ ((((p5 → p5) ∧ (p4 ∨ p5)) ∨ True) ∨ p2)) ∧ p1) ∨ ((p5 ∧ p1) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210061520188043113259410831182 : ((((True ∧ p4) ∧ False) ∨ True) ∧ ((True ∧ (True ∧ (False ∨ (p4 ∨ (((p2 ∨ True) → p4) → ((p2 ∨ (p4 ∨ True)) ∧ (True ∨ p5))))))) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_660832717627552567572072310657 : (((((p1 ∧ (((False ∧ ((((False ∨ True) → p1) ∧ (((False → p2) ∧ p2) ∧ p4)) ∧ p5)) ∨ False) → (False ∨ p3))) → p4) → (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773279602590369393938721281728 : (((False ∨ ((((((p5 → False) ∧ p4) ∧ p1) ∧ p5) ∨ (((p3 ∧ (p3 ∧ ((p5 ∧ False) ∨ p1))) → (p1 ∨ (True ∨ p1))) ∧ p5)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



