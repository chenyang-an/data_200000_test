variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201040073853828105169317036470 : ((p4 ∨ ((p4 → True) ∨ (p2 ∧ (p4 ∨ p4)))) → ((p3 ∧ (p4 ∧ p4)) ∨ (p4 ∨ ((False ∧ p1) ∨ (p5 → (True ∨ ((p2 ∨ p3) → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65314846279022095044547754181 : ((p3 ∨ ((((p2 ∨ (p2 ∨ (((p5 ∨ ((((p4 → p3) → p3) → p5) → True)) ∨ p1) → p2))) ∨ p3) → p4) ∨ (p4 → (p5 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301387254556720424240121680203 : (False ∨ ((False ∧ (p3 ∨ (p4 ∧ p1))) ∨ ((True → (((p1 ∨ (((False ∨ False) ∧ ((p2 → False) → p1)) ∧ (False ∨ p2))) ∨ p1) → p1)) ∧ True))) := by
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
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693974135344342136060416263155 : ((((((True → p4) ∨ (((p1 ∧ p1) ∨ p5) ∧ (p2 ∨ p2))) ∨ (True → True)) ∨ ((((p3 ∧ p3) ∨ p3) → p4) → ((p1 → p5) ∧ p3))) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313325523278619172731243969393 : (p3 ∨ ((p4 ∨ (((p2 ∨ ((True ∧ p1) ∨ ((True → ((p5 ∧ False) ∧ True)) → p4))) ∨ (p3 ∧ (((True ∨ False) ∧ p2) ∧ False))) ∨ p4)) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119049317009674774239236575899 : ((p1 → (((((p2 ∨ (True ∨ p4)) ∧ (False ∨ True)) ∧ p5) ∨ (p4 ∨ (True → ((p3 ∧ False) ∨ (True ∨ (p1 → True)))))) ∨ p2)) ∨ (p2 ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147734069492909181376789482939 : (((((p3 ∨ (p4 ∧ p4)) ∧ p2) ∧ (True → (((p5 ∧ (True ∨ p5)) ∨ p5) → ((p3 ∧ p2) ∧ p2)))) → p4) ∨ (p4 → ((True ∨ p5) ∨ p3))) := by
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
theorem thm_5_vars_117480378598731289635638095787 : ((p1 ∧ (p2 ∨ ((p2 ∨ (((p2 ∧ (p2 ∨ (True → p1))) ∨ (p5 ∧ (((p3 → p2) ∧ (p3 → p5)) → p4))) ∨ p4)) ∧ False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_240457303620204191056590874926 : ((p5 ∨ True) ∧ ((p3 ∧ p3) ∨ (p3 → ((p4 → p5) ∨ ((p5 ∨ (p4 ∨ ((False → p5) → ((p2 ∨ ((p2 ∨ p4) → p2)) ∨ p3)))) ∨ False))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624025529114592422817001082920 : ((((p2 ∨ ((p3 ∨ (False → ((((p3 ∨ ((p2 → p2) ∨ (p2 → (p4 ∨ p2)))) → p1) ∧ p5) → p5))) → ((True ∧ p5) ∧ p2))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632741874363505176250288677110 : ((((((((((p4 ∧ p3) ∧ (p5 ∨ ((((p1 → p4) ∧ p4) → p5) ∨ (p5 → p2)))) ∧ p3) ∨ False) → False) ∧ p1) ∧ (True ∧ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232465035832973603056834940282 : ((True ∧ (p1 ∨ p4)) → (((False ∨ (((p3 → False) ∨ p4) ∧ p3)) ∧ ((p2 ∨ p3) ∧ (True → p2))) → ((p1 ∨ ((False → p2) ∨ False)) → p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h6.left
        let h13 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h1.left
          let h16 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h18 =>
            -- One of the premise coincides with the conclusion.
            exact h14
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h1.left
          let h21 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h23 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h19
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h24 := h11 h23
            -- False on the left can always be used.
            apply False.elim h24
          case inr h25 =>
            -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
            have h26 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h19
            -- We have shown the premise of h11, we can now drive its conclusion.
            let h27 := h11 h26
            -- False on the left can always be used.
            apply False.elim h27
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h6.left
        let h30 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h1.left
          let h33 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h35 =>
            -- One of the premise coincides with the conclusion.
            exact h31
        case inr h36 =>
          -- Conjunctions on the left can always be decomposed.
          let h37 := h1.left
          let h38 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
            have h40 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h30, we can now drive its conclusion.
            let h41 := h30 h40
            -- One of the premise coincides with the conclusion.
            exact h41
          case inr h42 =>
            -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
            have h43 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h30, we can now drive its conclusion.
            let h44 := h30 h43
            -- One of the premise coincides with the conclusion.
            exact h44
  case inr h45 =>
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h2.left
      let h48 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h47
      case inl h49 =>
        -- False on the left can always be used.
        apply False.elim h49
      case inr h50 =>
        -- Conjunctions on the left can always be decomposed.
        let h51 := h50.left
        let h52 := h50.right
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h48.left
          let h55 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h54
          case inl h56 =>
            -- Conjunctions on the left can always be decomposed.
            let h57 := h1.left
            let h58 := h1.right
            -- Disjunctions on the left can always be decomposed.
            cases h58
            case inl h59 =>
              -- One of the premise coincides with the conclusion.
              exact h56
            case inr h60 =>
              -- One of the premise coincides with the conclusion.
              exact h56
          case inr h61 =>
            -- Conjunctions on the left can always be decomposed.
            let h62 := h1.left
            let h63 := h1.right
            -- Disjunctions on the left can always be decomposed.
            cases h63
            case inl h64 =>
              -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
              have h65 : p3 := by
                -- One of the premise coincides with the conclusion.
                exact h61
              -- We have shown the premise of h53, we can now drive its conclusion.
              let h66 := h53 h65
              -- False on the left can always be used.
              apply False.elim h66
            case inr h67 =>
              -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
              have h68 : p3 := by
                -- One of the premise coincides with the conclusion.
                exact h61
              -- We have shown the premise of h53, we can now drive its conclusion.
              let h69 := h53 h68
              -- False on the left can always be used.
              apply False.elim h69
        case inr h70 =>
          -- Conjunctions on the left can always be decomposed.
          let h71 := h48.left
          let h72 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h71
          case inl h73 =>
            -- Conjunctions on the left can always be decomposed.
            let h74 := h1.left
            let h75 := h1.right
            -- Disjunctions on the left can always be decomposed.
            cases h75
            case inl h76 =>
              -- One of the premise coincides with the conclusion.
              exact h73
            case inr h77 =>
              -- One of the premise coincides with the conclusion.
              exact h73
          case inr h78 =>
            -- Conjunctions on the left can always be decomposed.
            let h79 := h1.left
            let h80 := h1.right
            -- Disjunctions on the left can always be decomposed.
            cases h80
            case inl h81 =>
              -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
              have h82 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h72, we can now drive its conclusion.
              let h83 := h72 h82
              -- One of the premise coincides with the conclusion.
              exact h83
            case inr h84 =>
              -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
              have h85 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h72, we can now drive its conclusion.
              let h86 := h72 h85
              -- One of the premise coincides with the conclusion.
              exact h86
    case inr h87 =>
      -- False on the left can always be used.
      apply False.elim h87



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115408158973898652451639852105 : (((True → ((((p3 → p5) ∧ p5) ∧ p2) → p5)) ∧ (p5 → (((True → (False ∧ (False ∧ p3))) ∨ ((True ∨ True) ∨ False)) ∨ False))) ∨ (p3 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624829381457737052212047125848 : ((((p5 ∨ (((False ∨ (((False → False) ∨ (p2 ∨ p1)) → p2)) → (p2 → (((p3 ∨ (p1 ∨ p5)) → p5) → False))) ∨ (True ∨ p3))) ∨ False) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49247664608318739285410867551 : ((((p5 → p2) → (((True ∨ p2) → p3) ∨ (p2 → ((p3 → (True → (p2 → p2))) ∧ ((p5 ∧ p2) → p5))))) ∨ (p3 ∨ (True ∧ p1))) ∨ False) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53900815627275430627669209328 : (((p3 ∧ (((p1 → (p3 ∧ p4)) → p5) ∧ (p5 → p1))) ∨ ((p4 ∧ p3) ∨ ((p3 ∧ p4) → ((p5 → ((True ∧ True) ∨ p2)) ∨ p3)))) ∨ p1) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345665719040409237376935019739 : (p3 → ((False ∨ ((((p5 ∧ (p5 ∨ (False ∨ p4))) ∨ ((p3 ∧ p1) ∧ ((p5 ∨ (p2 ∨ p5)) ∨ True))) → p2) ∨ (p3 → (False → False)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345455803248823297997178888202 : (p3 → ((((((p3 ∧ True) ∨ ((p4 ∧ True) ∧ p5)) ∧ (((False ∧ (p5 ∧ False)) → p1) ∨ False)) ∧ ((p1 → p2) ∨ p2)) → (p1 ∨ p3)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304034362295637257542109461113 : (p1 ∨ ((p3 ∧ (((p5 ∨ (False ∨ ((p1 ∨ (p1 ∧ p1)) → (p5 ∨ (p5 ∨ (((p5 → p1) → p1) ∨ False)))))) ∧ (p1 ∨ p3)) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157442651590236270939013254155 : (((p4 ∨ ((p4 ∧ (p3 ∨ (False ∧ (p4 ∧ ((p3 → p4) ∧ (p1 ∨ p2)))))) ∧ p5)) ∧ (p5 → False)) ∨ (False → ((p1 → (True ∨ True)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58502829841847660445295631792 : (((p4 ∨ p4) ∧ ((p4 ∨ (((p2 ∧ True) ∧ (((False → (False ∨ p5)) → True) ∨ p5)) → (p3 ∨ (p3 ∨ p2)))) ∨ ((p4 ∨ False) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46923512545806019867274665015 : (((((p1 → (True ∨ p2)) ∧ ((p5 ∨ ((p4 ∧ p1) ∧ False)) ∧ (((p2 → ((p3 ∧ False) → p3)) ∧ p5) ∧ p3))) ∨ p2) ∨ (p1 ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98812984417359096753489748900 : ((True → ((((((p5 ∨ p2) → p4) ∧ (True ∧ p2)) ∧ p3) ∧ ((False ∧ (((True ∨ p1) ∨ p4) → (p1 → True))) ∧ (False ∧ p3))) ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354823094799614985260769466113 : (p5 → (((p4 ∧ (False ∨ False)) ∨ ((((p3 → ((((True ∨ p2) → ((False ∨ p5) → p5)) ∨ False) ∧ p3)) ∨ False) ∧ (p2 → p3)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42844635153092569438588509008 : (((p2 → (((False ∨ ((p3 ∨ ((p2 ∧ (p1 ∧ p4)) → (p1 ∧ ((p3 ∨ p4) ∨ ((p5 → p1) ∨ p4))))) ∨ p3)) → p4) ∨ p2)) ∨ p4) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340019263431757599170777276631 : (p1 → (p1 → (p4 → ((False ∨ ((((p2 ∧ p5) ∧ (p3 ∨ (True → p3))) ∨ p2) ∨ (True ∧ p4))) ∧ ((p1 ∨ (p3 ∨ (p2 ∧ p1))) ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677071179416036998093169026379 : ((((p3 → ((p1 → True) ∧ ((p4 ∨ (((False → False) ∨ False) ∧ p1)) ∨ (p5 → ((p5 → p4) → True))))) ∧ (p4 ∨ ((p2 ∨ p5) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_441923499910649121669440976210 : (((((((p4 ∧ p4) → ((False ∧ (p4 → True)) ∧ ((((p3 ∨ p5) → (p4 → p4)) ∨ p2) ∨ False))) → p2) ∧ p4) ∨ (p2 → (True → p2))) ∧ True) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192423941128318708590816479881 : ((((p2 → ((p1 ∧ (p5 ∨ p3)) ∧ p1)) ∨ True) ∨ p1) → (True ∧ (((p1 ∨ p2) ∧ (True ∨ p2)) ∨ ((p1 → (True ∧ p4)) ∨ (True ∨ p1))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159708916225731646889142856318 : ((((((p3 ∧ ((p1 → (False ∧ p2)) ∨ True)) → False) → (True → p1)) → (p2 ∧ (p5 ∨ True))) ∨ p2) → (((p1 ∨ (True ∧ p5)) ∨ p2) ∨ True)) := by
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
theorem thm_5_vars_642727799232339255033238803044 : ((((p1 ∧ ((p1 ∨ p2) ∨ ((False ∧ (False ∨ True)) → (((p4 ∧ (p1 ∨ (((True ∧ p2) ∧ p3) ∧ (p4 → True)))) → p5) → p3)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326116364125423776009356643437 : (p5 ∨ (p1 → ((((((p4 ∧ p1) ∧ p4) → (False → (p3 ∧ (p2 ∧ (p4 ∧ False))))) → False) ∧ (p5 → p2)) → (p3 → ((p3 → False) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : (((p4 ∧ p1) ∧ p4) → (False → (p3 ∧ (p2 ∧ (p4 ∧ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h10 := h5 h7
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h13 : (((p4 ∧ p1) ∧ p4) → (False → (p3 ∧ (p2 ∧ (p4 ∧ False))))) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h15
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h16 := h11 h13
  -- False on the left can always be used.
  apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3304113639547157788634207311 : ((p1 ∧ p1) → (((((False → True) → (p2 ∨ (p5 → (True ∧ p4)))) → (((p1 ∨ (True ∨ (False ∨ False))) → p5) ∧ p4)) ∧ p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221411317055481966763859307946 : (((True → p3) ∨ True) ∧ (((p4 ∨ (((p4 ∧ (True → (True → (False ∨ (p4 ∨ (True → True)))))) → False) ∧ ((p2 → True) ∧ p5))) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323808061334823214922302233979 : (p5 ∨ ((p1 ∨ ((((False ∧ ((p1 ∧ False) ∨ (True ∨ p1))) ∨ p4) ∨ (p5 ∧ (p2 → p2))) → p4)) ∨ (True ∨ (False ∨ ((p2 → p1) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56182500055212146091388405080 : (((p3 ∧ (p4 ∧ (p3 ∨ p3))) ∨ (((p3 ∧ p4) → ((p5 ∨ (p2 ∨ ((False → p4) ∨ ((True ∧ p5) ∨ False)))) ∧ (True ∨ p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606402769974788519536829215645 : ((((((((p3 → p2) → p3) ∧ (p2 → ((True → ((p5 → p5) ∨ (((p2 → (p2 ∧ True)) ∨ False) ∧ p4))) ∧ p4))) ∨ False) ∧ False) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_61388159190199627682522422209 : ((p1 ∧ (((((p1 → (((p5 ∧ (p5 → True)) ∧ True) ∨ p4)) → p5) ∧ p1) ∨ (p1 → (((False ∧ (True ∨ p2)) ∨ True) ∨ p2))) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662439132165968746153396644246 : (((((True ∨ ((p2 → ((p4 → p3) → p5)) ∧ p2)) → (((p4 ∧ True) ∧ ((p3 ∧ (True ∨ (p2 ∨ p3))) ∨ False)) → False)) → (p4 ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317707813603082690189708503848 : (p4 ∨ ((((True → (p2 ∧ ((True ∨ (True ∧ p5)) ∧ (p4 ∨ p2)))) ∨ ((True → True) → (False ∨ (p4 ∧ (p5 → p3))))) ∨ (p3 → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348149183411624647556482733257 : (p3 → ((p4 ∧ p5) → ((False ∧ (p2 ∨ ((False ∧ (False ∧ (((p3 ∨ p3) → p3) ∨ p2))) ∨ ((p1 ∧ ((p2 → p2) ∧ False)) ∧ True)))) ∨ p5))) := by
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
theorem thm_5_vars_263141291598710847020283404050 : (True ∧ (((p2 ∧ p5) ∧ ((((p1 → (((p5 ∨ p2) → p4) ∨ (p5 → p5))) ∧ ((True → p4) → (p4 ∨ p4))) → p5) → p2)) ∨ (p3 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119903914973182662369397215652 : (((((p3 ∧ ((True → (((((p4 → (p4 ∨ (p5 → p1))) ∨ p4) → p5) ∧ p4) → p4)) → p2)) → p1) → (p2 ∧ p5)) ∧ p1) → (p4 ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ ((True → (((((p4 → (p4 ∨ (p5 → p1))) ∨ p4) → p5) ∧ p4) → p4)) → p2)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49314366506588551666699011129 : (((p2 ∨ ((False ∧ p3) ∨ ((p4 ∨ (p4 → ((True ∨ p4) ∧ ((((True → p4) → True) ∧ p5) → p2)))) ∨ p4))) ∨ (p4 ∨ (p5 ∨ True))) ∨ False) := by
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
theorem thm_5_vars_718047694956901082900168773626 : ((((((p2 ∨ p4) ∨ p3) ∨ p2) ∨ ((p4 ∨ (((True ∨ (p1 ∧ (p4 → p2))) → p3) ∧ ((p4 → p2) → (p4 ∨ p5)))) ∨ (p3 ∨ True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656998573182654628770120614674 : (((((p4 ∨ (p1 ∨ (p4 ∧ p2))) → (p1 ∨ ((((False → p2) ∧ (False ∨ p4)) → (p5 → (p4 ∧ (p3 ∧ p2)))) ∨ p3))) ∨ (p4 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_600462803309726016524271786659 : ((((True ∧ (((p5 → p2) ∨ (p2 ∧ ((p4 ∨ (p5 ∨ p5)) → (p5 ∧ p5)))) → ((p2 ∨ p1) ∧ ((p2 ∨ p2) → (p3 ∨ p1))))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87400558491568968396940098905 : (((p4 ∧ (True ∨ (False ∨ (p4 ∨ p3)))) ∧ (((p5 ∨ (p5 ∨ (((((True ∧ True) ∨ (p2 ∧ p1)) ∧ False) ∨ p2) ∨ p4))) → False) ∨ p1)) → p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h8 : (p5 ∨ (p5 ∨ (((((True ∧ True) ∨ (p2 ∧ p1)) ∧ False) ∨ p2) ∨ p4))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h9 := h7 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h15 =>
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h16 : (p5 ∨ (p5 ∨ (((((True ∧ True) ∨ (p2 ∧ p1)) ∧ False) ∨ p2) ∨ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h17 := h15 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h20 =>
          -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
          have h21 : (p5 ∨ (p5 ∨ (((((True ∧ True) ∨ (p2 ∧ p1)) ∧ False) ∨ p2) ∨ p4))) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h20, we can now drive its conclusion.
          let h22 := h20 h21
          -- False on the left can always be used.
          apply False.elim h22
        case inr h23 =>
          -- One of the premise coincides with the conclusion.
          exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52616755761520549312329261885 : ((((True ∧ (True ∨ p2)) ∧ (p4 ∧ ((((False ∨ p2) → p2) → False) ∨ p1))) ∨ ((((p1 ∧ p5) → p2) → ((p1 → p1) → False)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674216137211499674861984414486 : ((((p5 ∧ (((p2 ∨ ((p4 ∨ (p4 ∧ ((p5 → (p3 → False)) ∨ p4))) ∨ (p1 ∧ p3))) ∨ p2) → (p1 ∧ True))) → (False ∧ (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336232573856705362273121441453 : (p1 → ((((p1 → ((False → p5) → False)) ∧ (True ∨ (False → (p1 ∨ (((p2 → p2) → (p5 ∨ p3)) ∧ p3))))) → ((True ∧ p5) ∧ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- False on the left can always be used.
      apply False.elim h9
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h14
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h2.left
  let h18 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h20 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h21 := h17 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h24 := h21 h22
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h26 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h27 := h17 h26
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h28 : (False → p5) := by
      -- Implications on the right can always be decomposed.
      intro h29
      -- False on the left can always be used.
      apply False.elim h29
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h30 := h27 h28
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655910096105697222207699497727 : (((((((((p4 → (p3 ∨ (p5 ∨ p1))) ∧ p3) ∨ (p2 ∧ p2)) → (p2 ∧ p2)) ∨ p5) ∧ ((p5 → (p5 ∨ p5)) → p4)) ∨ (True ∨ p4)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_339137796180207704195535761569 : (p1 → (p1 ∧ ((((p1 ∨ (True → ((p3 ∧ False) → ((p2 → True) → True)))) → p2) ∨ True) ∨ ((p4 ∨ (p1 ∨ ((p3 → p1) → p1))) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135594011701335851678369331186 : (((((p3 ∧ (((p3 ∨ p1) → p4) → False)) ∨ p4) ∨ ((p1 ∧ (p1 ∧ p3)) ∨ p5)) ∨ ((False ∧ True) ∧ (p5 → p4))) ∨ ((p5 → p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305025378370192270707257080887 : (p1 ∨ ((p2 ∧ ((p3 → (p2 ∧ (p4 ∨ p5))) ∨ ((p4 ∧ True) ∧ ((((p2 ∧ p5) → p2) ∨ (p3 → p2)) ∨ p2)))) ∨ ((p4 ∨ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47377687884052602321700839803 : ((((p3 ∧ p1) → (True ∧ (((False ∨ ((False ∧ p4) ∨ ((p3 ∧ p4) ∧ (p5 ∧ p4)))) ∧ (p4 → p3)) ∧ (p2 ∨ p1)))) ∨ (p4 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215003401074029361923670209980 : (((True ∨ p3) → (p1 ∨ p4)) ∨ ((False ∨ p1) ∨ (((p2 ∧ (p5 → (((p5 ∨ (True → ((True ∧ p4) ∧ p2))) ∧ True) → p5))) ∧ False) → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319412667156109088346050290944 : (p4 ∨ ((p5 ∨ ((p3 ∧ True) ∧ (True ∨ ((p5 ∨ True) → ((p2 ∨ p3) → False))))) → (p3 → ((p2 ∧ (False → p5)) → ((p4 ∧ p5) ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_237960415095650011407799562049 : ((True ∨ False) ∧ (((p1 ∨ (p5 ∧ (p3 ∨ p3))) ∧ True) → (((False ∧ (p4 → (True ∨ p2))) ∧ ((p4 ∨ p4) ∨ (p1 ∨ (p2 ∧ p1)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313138220420574946354353615675 : (p3 ∨ (((((((p2 ∧ (p1 ∧ p2)) → (p2 ∧ p1)) → (p1 ∧ p1)) ∧ p4) ∨ (p5 → p1)) ∨ ((((p2 ∨ p3) ∧ p2) → True) ∨ p4)) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172863958079878714533406598900 : ((False ∧ (p4 → (p4 ∧ (((p2 ∧ p5) → ((p3 → (p4 ∧ p1)) ∧ p4)) ∨ True)))) ∨ (((p2 ∨ False) ∨ (False ∨ p5)) ∨ ((False ∧ p3) → p4))) := by
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
theorem thm_5_vars_184633462705055437422906333852 : (((False ∨ ((True → True) ∧ (p3 ∨ p5))) ∧ (False ∧ (True → p3))) ∨ (p4 → ((False ∧ (p1 ∨ True)) ∨ (p3 → (True ∨ ((p4 ∧ False) → p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697652893723914909122383743310 : ((((p4 ∨ (((True → (False ∨ p3)) ∨ False) ∧ ((p5 ∨ p5) ∨ p4))) ∧ (((True ∧ p3) ∧ p2) → (((p4 → True) ∧ (p2 ∨ p1)) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740095460000320936798350029133 : ((((False ∨ p2) ∨ ((p1 ∨ (((p2 ∧ p3) → p5) ∧ p1)) → ((((False ∨ (True → True)) ∧ p4) ∧ ((p5 → (p3 → p2)) → p1)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65862029756457594779201946731 : ((p4 ∨ ((p4 ∨ p5) ∧ (((p1 ∨ p2) → (True ∧ (p1 → p2))) → (((p5 ∧ (((p4 ∧ True) ∧ p4) → p5)) ∨ p5) ∧ (p5 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49663629990160992633616320777 : ((((p4 ∧ (True → p3)) ∨ ((p4 ∨ (p2 ∧ ((p4 ∧ (((p5 ∧ p1) ∨ False) ∧ (p2 ∧ p4))) ∨ p1))) ∨ p1)) → ((p5 → p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114610030611531502276479585991 : (((p5 ∨ ((((((p5 ∨ p1) ∨ False) ∧ p1) ∧ (p5 ∨ (p3 ∧ p5))) ∨ p4) ∧ p4)) ∧ (False ∧ ((p4 ∧ p3) ∨ (p1 ∨ p3)))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768762256105994876992973717444 : (((p5 ∧ (((False ∧ (p3 ∨ True)) ∨ ((p2 ∧ False) ∨ p1)) ∨ ((p3 ∧ ((True ∧ ((p2 ∨ p3) ∨ p5)) ∧ p1)) ∧ ((p4 ∨ p2) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259665110524568375745274351382 : ((p1 → False) → (p2 → (p3 → (((True ∧ (True ∧ (p1 ∧ ((((p4 ∧ p4) ∧ p1) → p5) ∨ p4)))) → ((p3 ∧ False) ∨ p4)) ∨ (p5 → p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h11 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h13 := h1 h12
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693495375351281480124008410997 : ((((((((p2 ∨ p5) ∧ ((True ∧ p3) ∨ p4)) → (p5 ∨ p3)) → p4) ∧ p5) ∨ (False → ((((True ∨ True) → True) ∨ p1) → (True → p1)))) ∨ p5) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42184365342887142326644598844 : (((True ∧ ((((True ∧ (((((p1 → p1) ∨ p2) ∨ False) → p4) ∧ p2)) ∨ p5) ∧ (False → ((p4 ∨ False) ∧ p5))) → (p1 → p5))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47528016630023118342581393112 : (((p4 ∨ ((p4 ∧ (p4 → ((p5 ∨ p3) → (p1 ∧ (((((p5 → p3) → p2) ∨ p2) ∨ p1) ∧ (p4 → p2)))))) ∧ p5)) ∨ (p4 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198551413034375928199901550009 : ((p1 ∨ ((((p2 → p5) → p2) ∧ False) ∧ p1)) ∨ ((p4 → p2) → ((True ∧ (p2 → True)) ∧ (True ∨ (p1 → ((True ∨ False) ∨ (True ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631610749831435629715737856250 : (((((((((p2 ∨ (p1 → (p5 → (p5 ∧ (p4 ∨ True))))) ∧ False) ∨ p4) ∨ (p3 → False)) ∨ (p5 ∧ ((True ∨ True) ∨ True))) → True) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784399365950708518126269925723 : (((p3 ∨ (p3 ∧ (True → ((p3 ∨ False) → (((p2 ∨ (((p5 → p4) ∧ (False → (p1 → (True ∧ p4)))) → True)) ∧ p2) → (p2 ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752999394453255066615015415338 : (((False ∧ ((((p1 ∧ p5) → ((p1 → p1) ∧ p1)) ∧ ((True ∧ p2) ∧ (False → (((p3 ∨ (p4 ∧ p4)) → (p4 ∧ True)) ∧ p3)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178740935800004267887147471773 : (((False ∨ (p4 ∨ (p1 ∧ p5))) → ((p5 → (True ∧ (True ∨ p3))) ∧ p1)) ∨ ((False ∧ p3) ∨ (((p3 ∧ p1) ∨ True) ∨ ((p5 → p2) → True)))) := by
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
theorem thm_5_vars_48766267875604339255411869618 : ((((p2 ∨ p1) ∨ ((((((False ∨ p5) ∨ (p5 → p1)) → p2) ∨ p1) ∨ (p1 ∨ (p1 → False))) ∧ (False ∨ p4))) ∧ ((p2 → p4) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213144568203264018828112015186 : ((((p5 → p5) ∧ p3) ∧ True) ∨ (((p2 ∨ (p4 ∨ False)) ∨ p4) ∨ (((((((p1 ∨ p2) → (p3 ∨ True)) ∨ False) ∨ True) ∧ p4) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64955847899422477039531483225 : ((p2 ∨ ((((((p5 → p2) ∨ p5) ∧ True) ∨ p1) ∧ p5) ∨ ((p3 ∨ (p4 → p3)) → (p4 ∧ ((p5 ∧ False) → ((p1 ∧ False) ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799605220083124747255649051268 : (((p1 → (p5 ∨ ((((p1 ∨ True) → ((p5 ∧ ((p3 ∧ (p5 → p3)) ∨ p5)) ∧ (False ∧ p3))) ∧ (False → (p4 → (p2 ∧ p1)))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349971907278651360121114218180 : (p4 → (((p2 → ((((p2 ∨ (((((p5 ∨ ((p1 ∧ p2) → p2)) ∧ p5) ∧ False) ∧ p5) ∨ (False ∨ True))) → p4) → p5) ∧ p5)) ∧ False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190789399904376439806563698565 : ((((p2 → ((p3 ∨ p3) ∧ p2)) → p4) ∨ (p2 ∨ p1)) ∨ (((((False ∨ ((p2 ∧ p2) ∨ p1)) → p5) → p3) ∧ (p5 → (True ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651476830721496133911438038773 : (((((p2 → (p3 ∨ p4)) → ((True → (p3 ∧ ((((True ∧ (True → p4)) ∨ False) → p1) ∧ (p3 → p1)))) ∨ (p1 ∨ False))) ∧ (p2 ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49309859698345919449923901279 : (((p1 ∨ (p1 → ((((p1 ∨ p3) ∨ ((p2 → p3) ∧ (p3 → p4))) ∧ True) ∧ (((p4 → p1) ∨ p4) → p2)))) ∨ (p2 ∨ (p1 ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58843964269592341314741038598 : (((True ∧ p2) ∨ (((p1 → (p5 ∨ (p3 ∧ p4))) ∨ ((p2 → (True ∨ ((((True → p2) → p4) ∨ p5) ∧ p3))) ∧ (p1 ∨ p2))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41372086449404546383932071515 : (((((False → True) → (p2 → (False ∨ ((p2 → (p1 ∧ (False ∨ (True ∨ p5)))) → p1)))) → (p4 ∨ ((p5 ∧ (p2 → p2)) → p4))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59658196403420793525553679144 : (((True ∧ True) → (p2 ∨ (((p3 → ((p5 → ((p1 → p2) ∧ (p4 → (p4 → p3)))) ∨ ((p3 ∧ True) ∧ (True ∧ p1)))) ∧ p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313947074568667085364566861652 : (p3 ∨ ((((p1 ∨ (p1 → (True ∨ True))) → (((p3 ∧ p4) → p2) → ((p5 → (((p3 ∨ p1) → False) ∧ p4)) ∧ False))) → False) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358491830411897929788541251501 : (p5 → (p1 → ((p1 ∨ p3) ∧ ((p3 → (False ∧ ((((p5 → (p4 ∧ False)) → (((p4 ∨ p3) ∨ p2) → p1)) → True) → p2))) ∨ (p5 ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199563787707874518875562033282 : ((((((True ∧ p4) → p4) → False) ∨ p5) → p2) → ((False ∨ (False ∧ (p5 ∧ (p4 → (p5 ∧ (False → (p5 ∨ p3))))))) ∨ ((p5 ∧ p3) → p3))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781758216664099911151593992818 : (((p2 ∨ (p5 ∨ (((((p2 → False) → (False ∧ (True ∨ p1))) ∧ (p2 ∨ ((False → p4) ∨ p4))) ∨ True) ∨ (((False → True) ∧ p2) ∧ p1)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50369900231473268440635938038 : ((((p5 → (p2 ∨ p2)) ∨ (p5 ∧ ((p5 ∨ True) ∨ ((True ∧ (((p3 → p4) ∧ p3) ∨ True)) → p2)))) ∨ (p3 ∨ (p5 → (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802404295378239320761175894181 : (((p2 → (False ∨ (False ∧ ((p4 → (True ∧ ((False ∨ False) ∨ ((((p3 ∨ False) ∨ p1) ∨ ((p2 ∧ p3) → p5)) ∧ (False ∨ p3))))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630502062313723961863798879975 : (((((p1 ∨ (((p5 → (p2 → p2)) → ((p1 ∨ True) ∨ (p1 → (p3 ∨ (p2 → (p2 ∨ (p5 → p5))))))) ∧ (p4 → True))) ∨ p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1490671811589079357448892111 : (((p2 ∨ (((p2 ∧ (p3 ∨ p2)) → ((p3 ∧ ((p4 → ((p5 ∨ p2) ∨ p4)) ∧ p4)) ∨ p1)) ∨ True)) ∧ (p2 ∨ True)) ∨ (p3 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_178354801249533327445320076586 : (((p2 ∨ (((p3 → (True ∨ p3)) → p5) ∨ (p5 ∨ p1))) ∨ (p1 ∧ p2)) ∨ (False → ((p2 ∨ ((False → (p3 ∨ p2)) → p5)) ∧ (p1 → p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165512905331055099118587057939 : ((((((p5 ∨ p1) ∨ p3) → ((p4 ∨ p5) → p5)) → False) → (((p5 → False) ∨ p5) ∧ p1)) ∨ (p4 ∨ (p5 ∨ (p5 → ((p4 → p3) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_38752725945658598193255552960 : (((((p1 ∨ True) ∧ (p1 ∨ p5)) ∧ ((p4 ∨ ((True ∧ (p4 ∧ True)) ∧ False)) → ((p5 → ((p5 ∨ (p4 ∨ p1)) ∧ p4)) → p5))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305160832786507148312221392879 : (p1 ∨ (((((p1 ∧ True) ∨ False) ∨ (False ∧ ((True ∨ ((((p3 ∧ True) ∨ p4) ∨ p5) ∨ p5)) ∧ p4))) ∨ p4) ∨ ((True ∧ True) → (p5 → True)))) := by
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



