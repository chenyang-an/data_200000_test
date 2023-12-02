variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41507166543841301662009716734 : ((((p5 ∨ ((((p2 → p1) → ((p4 ∧ p4) ∨ p4)) → p5) → p4)) → ((p2 ∧ ((True ∨ p2) → False)) → (p4 → (p3 ∧ p1)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306610080912674353892478485052 : (p1 ∨ ((p3 → True) → ((((p3 ∨ p4) → (False ∧ ((p3 ∨ p3) → (p3 ∨ (p3 ∨ (((p5 ∧ True) → p3) ∧ p2)))))) ∧ (p4 ∧ True)) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (p3 ∨ p4) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327309767617516115183074932983 : (True → ((((p5 ∨ p3) ∧ ((((p2 ∨ p3) → ((p2 → p2) ∨ p1)) ∨ (True ∨ p5)) → ((((True → p4) ∧ p5) ∧ p2) ∧ p1))) ∨ False) → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (((p2 ∨ p3) → ((p2 → p2) ∨ p1)) ∨ (True ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h7
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (((p2 ∨ p3) → ((p2 → p2) ∨ p1)) ∨ (True ∨ p5)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228861502960654971616565260415 : ((p3 ∨ (p4 → p5)) ∨ ((p3 → (False → (p4 → (p5 ∨ p5)))) → (((p1 ∧ False) ∨ (((False ∨ p4) → (p2 ∨ True)) → (p5 ∧ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245300051432266116329379512368 : ((p2 ∧ p2) ∨ ((p2 ∨ (((p2 → ((p2 ∨ (p4 ∨ p1)) ∧ ((p5 ∧ p1) ∨ (True → p4)))) ∧ p1) ∧ p1)) ∨ (True ∨ ((p5 ∧ True) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177854391822674297514809012192 : (((((False ∨ (p3 ∨ (False ∨ ((p1 ∨ p4) ∨ p5)))) ∨ True) ∨ p4) ∨ True) ∨ (p3 → ((((p5 ∨ p2) ∧ p4) ∧ ((p3 ∨ p1) → False)) → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51170124866086813059053836265 : ((((((True ∨ (p3 → (((False → False) ∧ True) ∨ p4))) → p3) ∨ (p3 → p2)) ∨ (False ∨ p2)) ∨ ((((False ∧ p2) → p3) ∧ True) ∨ p4)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_106514090244682517229009449906 : (((((p3 ∧ p1) ∧ (p2 ∨ p2)) ∨ (p4 ∨ True)) ∨ ((True → (p1 → ((p4 → p4) ∨ (p5 → False)))) → ((p5 ∧ True) ∧ p5))) ∧ (False → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133934884589033146561576672052 : (((True → (p5 ∨ (p1 → (((True ∧ False) → ((p5 ∨ p4) → ((False ∧ (p1 ∨ p1)) → (p4 ∨ False)))) → p3)))) ∧ False) ∨ ((False ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42024064184474043478799050087 : ((((p1 ∧ True) ∨ (((((p4 → True) → (p4 → p3)) → (False ∨ (p4 ∧ p2))) ∧ ((p4 → (p3 ∨ False)) ∨ False)) → (p1 → p2))) ∨ False) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p4 → True) → (p4 → p3)) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h9 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h10 := h5 h9
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- False on the left can always be used.
        apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h6
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h17
  case inr h18 =>
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725558818800058477194889056744 : (((((p1 ∧ p5) ∧ False) ∨ (p4 → (((False ∨ False) ∨ ((True → p1) ∨ (p1 ∧ p3))) ∨ (p1 ∨ ((((p1 → p3) ∧ p3) ∧ True) ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56218299908616940960387879623 : (((p2 ∨ ((p4 ∧ p4) → p1)) ∨ (((((p1 ∧ p5) ∧ True) → ((p1 ∧ p1) ∧ (p2 ∧ p3))) ∧ (p3 → (p1 ∨ True))) ∨ (p4 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181338052000257162716584198663 : ((True ∨ (p1 → (True → ((p5 ∧ p3) → ((False → True) ∧ (False → False)))))) → (((p4 ∧ p5) ∧ (p5 → (False ∨ (p2 ∧ p2)))) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114598396767518741786513620935 : (((p1 ∧ (((p2 → ((p3 ∧ (False → p1)) → p1)) → ((False ∨ p2) → False)) ∧ p2)) ∧ (((p2 → p1) ∧ (p3 → p1)) → p3)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161990002594848153665809442986 : ((p3 → ((True ∨ ((((p3 → (p2 ∨ p3)) ∨ p2) ∨ False) → False)) ∧ ((p5 ∨ False) ∨ (False ∧ p3)))) → ((((p5 → False) → p5) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114009806865865313318885832158 : ((((True ∧ (p4 ∨ (((p4 ∧ p5) ∨ True) ∧ ((p3 ∧ p2) ∨ (((True ∧ p4) ∨ p5) ∨ p1))))) ∧ True) ∨ (p4 → (p4 → p4))) ∨ (p5 → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58402082365649285723147977583 : (((p2 ∨ False) ∧ ((p2 ∨ (((p5 ∨ (p1 → p5)) → (p5 ∧ p1)) ∧ (True ∨ p5))) ∧ (((p4 → True) → ((True → True) ∧ p5)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654427707069092797380285499488 : ((((((True → (p3 ∨ p1)) ∧ (((False → (True → p2)) → p4) → (p4 → (p5 ∧ (((True ∧ False) ∨ p5) ∧ True))))) ∨ True) ∨ (p5 → p1)) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637993462394135527547230076364 : ((((((((p5 ∨ p1) → (False ∧ False)) ∧ p5) → p2) ∨ ((((p4 ∧ ((p4 → (p4 → p5)) ∨ p5)) ∧ p1) ∧ p2) → (p3 ∧ p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50348548825439886475102098421 : ((((((False → p3) ∧ False) → p4) ∧ (((False → ((p4 ∧ p3) ∨ p2)) → p5) ∧ ((p2 ∧ False) ∨ p1))) ∨ ((p2 → (p3 ∧ p1)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217390223103858079254232989853 : (((True → (p3 ∧ False)) ∨ p4) → (((p3 ∨ True) ∨ ((p3 → p2) ∧ (((((p1 ∨ p5) ∧ (True ∨ True)) ∨ (True ∨ p3)) ∨ p4) ∧ p2))) → p4)) := by
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
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h6 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h7 := h5 h6
        -- We need to get the right conjuct of h7 based on <expert-advice>.
        let h8 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h13 := h11 h12
        -- We need to get the right conjuct of h13 based on <expert-advice>.
        let h14 := h13.right
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h26 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h27 =>
              -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
              have h28 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h27, we can now drive its conclusion.
              let h29 := h27 h28
              -- We need to get the right conjuct of h29 based on <expert-advice>.
              let h30 := h29.right
              -- False on the left can always be used.
              apply False.elim h30
            case inr h31 =>
              -- One of the premise coincides with the conclusion.
              exact h31
          case inr h32 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h33 =>
              -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
              have h34 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h33, we can now drive its conclusion.
              let h35 := h33 h34
              -- We need to get the right conjuct of h35 based on <expert-advice>.
              let h36 := h35.right
              -- False on the left can always be used.
              apply False.elim h36
            case inr h37 =>
              -- One of the premise coincides with the conclusion.
              exact h37
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h39 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h40 =>
              -- We want to use the implication h40 based on <expert-advice>. So we show its premise.
              have h41 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h40, we can now drive its conclusion.
              let h42 := h40 h41
              -- We need to get the right conjuct of h42 based on <expert-advice>.
              let h43 := h42.right
              -- False on the left can always be used.
              apply False.elim h43
            case inr h44 =>
              -- One of the premise coincides with the conclusion.
              exact h44
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h46 =>
              -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
              have h47 : True := by
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h46, we can now drive its conclusion.
              let h48 := h46 h47
              -- We need to get the right conjuct of h48 based on <expert-advice>.
              let h49 := h48.right
              -- False on the left can always be used.
              apply False.elim h49
            case inr h50 =>
              -- One of the premise coincides with the conclusion.
              exact h50
      case inr h51 =>
        -- Disjunctions on the left can always be decomposed.
        cases h51
        case inl h52 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h53 =>
            -- We want to use the implication h53 based on <expert-advice>. So we show its premise.
            have h54 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h53, we can now drive its conclusion.
            let h55 := h53 h54
            -- We need to get the right conjuct of h55 based on <expert-advice>.
            let h56 := h55.right
            -- False on the left can always be used.
            apply False.elim h56
          case inr h57 =>
            -- One of the premise coincides with the conclusion.
            exact h57
        case inr h58 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h59 =>
            -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
            have h60 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h59, we can now drive its conclusion.
            let h61 := h59 h60
            -- We need to get the right conjuct of h61 based on <expert-advice>.
            let h62 := h61.right
            -- False on the left can always be used.
            apply False.elim h62
          case inr h63 =>
            -- One of the premise coincides with the conclusion.
            exact h63
    case inr h64 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h65 =>
        -- One of the premise coincides with the conclusion.
        exact h64
      case inr h66 =>
        -- One of the premise coincides with the conclusion.
        exact h66



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116410481049044650576776815018 : (((False ∨ (p5 ∨ p2)) → (((((((p3 → p1) ∧ p4) ∨ p5) ∨ True) ∨ ((p1 ∨ p2) ∨ False)) ∧ p1) → (p5 ∧ (p1 ∧ p2)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731690039245184536708207988363 : ((((p2 → (p1 ∨ False)) → ((((p3 ∨ p3) ∨ ((p2 ∧ False) ∧ (True → p1))) ∨ (False ∨ ((p5 ∧ p2) ∨ p3))) → ((True → p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152387151420436268689625890666 : (((((p3 ∧ p5) ∨ p3) ∨ p2) → (False ∧ (((p1 ∧ p2) ∧ (p3 ∧ p1)) ∨ (p2 ∨ ((p5 ∧ True) ∧ p4))))) → ((True → p2) ∨ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∧ p5) ∨ p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49085475129675805509923366421 : (((((p5 → (((p3 → (False ∧ (((p4 → p5) → p5) ∧ p3))) ∧ False) ∧ p1)) ∨ p4) ∧ ((p4 → True) → False)) ∨ (False → (p5 → False))) ∨ p1) := by
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
theorem thm_5_vars_345485132020481983346526617653 : (p3 → (((False ∨ (p5 ∨ (True → (((p1 ∨ (False → p4)) ∧ ((p3 → True) ∧ (False ∨ p1))) ∧ p3)))) ∧ ((True → (p2 → p2)) ∧ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321748522156244378235479209329 : (p4 ∨ (p5 → ((p1 ∨ (p1 → False)) ∨ ((((((p5 ∨ p3) → (False → (p2 ∧ (p2 ∨ p1)))) ∧ False) ∨ ((False ∧ True) ∨ p2)) ∨ p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624158707308463448923096512679 : ((((p2 ∨ (p4 ∨ ((((((p3 → (p4 ∧ p1)) → (False ∧ False)) ∨ True) ∧ (p4 ∧ p5)) → p3) → (p1 → ((p1 ∧ True) ∨ p2))))) ∨ p5) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157360904133722645961456826022 : (((p1 → (True ∧ ((((p3 ∨ p5) ∧ (False → ((True → True) → p2))) → (False ∨ p1)) → p4))) → p4) ∨ ((False ∧ (p1 ∨ True)) → (p1 → p5))) := by
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
theorem thm_5_vars_207917027632311534069295667735 : (((p5 ∧ (p5 → p3)) ∧ (True ∧ p2)) → ((((((p3 → p4) ∨ (False ∧ False)) ∨ p1) ∨ True) ∨ False) ∨ ((True ∨ True) → ((p2 ∨ False) ∨ p4)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705891728203811580099339531658 : ((((((True ∨ p2) ∨ p4) ∨ (p5 ∨ (True ∨ p1))) ∧ ((p2 ∧ (((p5 ∨ True) → (p5 ∧ (True ∨ False))) ∧ p3)) ∨ ((False → p1) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164454540221066702309643745210 : (((((p5 ∨ p2) ∧ (p1 ∨ (p2 ∨ (True ∨ (False → ((False ∨ p2) ∨ p3)))))) ∧ False) ∧ p2) ∨ (((p1 ∨ p2) ∧ (False ∧ (False ∧ p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117201090813650680472442802375 : ((True ∧ ((((p3 ∨ (p1 ∨ ((p1 ∨ p1) ∨ p4))) ∨ p2) ∨ p3) ∧ ((p1 ∨ p2) ∧ (p5 → (((True ∧ p5) ∧ p2) → p5))))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264628125000042144762235079229 : (True ∧ (((p5 ∨ p2) → p5) → ((((p4 → (p1 ∨ (p4 ∧ ((p1 ∨ True) ∧ False)))) → ((False → p1) ∨ ((p4 ∨ p2) → p4))) → p2) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 → (p1 ∨ (p4 ∧ ((p1 ∨ True) ∧ False)))) → ((False → p1) ∨ ((p4 ∨ p2) → p4))) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p5 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147292221378652185756554635973 : ((((((p3 → False) ∨ (((((p4 ∧ (p5 ∨ p3)) ∨ p1) ∨ (p1 → p3)) ∧ p2) → False)) ∧ True) → p1) ∨ True) ∨ ((p4 → (p1 ∧ p1)) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707157161506143877410350614061 : ((((((False → p1) ∨ (p1 → (p1 → p2))) → p5) ∨ ((p4 → p1) → ((((p3 → p1) ∧ p1) ∧ ((p1 ∧ p3) → p1)) → (p5 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783008840454713947915374983127 : (((p3 ∨ ((((True ∨ p3) → p2) → ((False ∧ ((p4 → p5) → ((p1 → p4) → False))) ∨ (True → (False ∨ (False → p3))))) ∨ (p1 ∨ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_918875856397768488338456705529 : ((((((((True ∧ (p3 → p2)) ∧ True) → p2) ∨ (False → (p5 → p2))) → p4) ∧ ((False ∧ p4) → (p4 ∨ ((True ∧ (p4 ∨ False)) ∧ p1)))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∧ (p3 → p2)) ∧ True) → p2) ∨ (False → (p5 → p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118347819708141863468898461324 : ((p2 ∨ (((((p4 → (p4 → p1)) ∧ p4) ∧ ((False ∨ (((False ∨ False) → (True → (False → p4))) ∧ True)) ∧ True)) ∨ p5) → p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148108816760846229435838260340 : ((((((((True → (p1 ∧ True)) ∨ True) ∧ p3) → p2) ∨ p3) ∧ (p1 ∧ ((p4 → False) → p5))) → (p1 ∧ p1)) ∨ (False ∨ (p1 ∧ (False ∨ False)))) := by
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
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h11.left
    let h17 := h11.right
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798703871387817323471499936 : ((True ∧ (p5 ∨ ((p1 → ((p5 ∨ (True ∧ ((False ∨ p4) → ((p5 ∧ p3) ∨ (p2 → p2))))) ∨ (True ∧ (p1 ∧ p3)))) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83810874413866307125986098098 : ((((((True ∨ (False → ((False ∧ (p1 ∨ p4)) ∨ p3))) ∨ p5) → p1) ∨ ((True → p5) ∨ True)) → (p5 ∧ ((p4 ∧ False) ∧ (True → p2)))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((True ∨ (False → ((False ∧ (p1 ∨ p4)) ∨ p3))) ∨ p5) → p1) ∨ ((True → p5) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116900270804660207144910928337 : (((p4 → p5) ∨ ((False → (True → p1)) → (p4 ∨ (((p5 ∧ ((p2 ∨ False) ∨ p4)) ∨ True) ∨ ((p4 → p3) ∧ (p3 ∨ p2)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193809270556004211866930391133 : ((p5 ∧ ((True ∧ ((p5 ∧ p3) ∨ (p4 ∨ True))) ∨ p5)) → (p1 → ((True ∨ ((p1 ∧ True) ∧ p2)) → (((False ∨ p1) ∧ (p1 ∨ False)) ∨ p4)))) := by
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
    let h5 := h1.left
    let h6 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h15 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h16 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h1.left
    let h23 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h32 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h2
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h2
    case inr h33 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346396892491079939685968902692 : (p3 → ((p5 → ((((p1 ∧ (p5 ∧ (True ∨ p3))) ∧ (p1 → (p2 ∨ (p4 ∧ (True ∧ (p4 ∧ p5)))))) ∨ False) ∨ (False → p2))) ∨ (False ∧ False))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356106874712933269501510595695 : (p5 → (((True ∧ ((((p2 ∧ p1) ∨ p3) ∧ (p4 ∨ False)) ∧ ((True → (True ∨ False)) ∧ False))) ∨ p5) ∧ ((p1 ∨ (p5 ∨ (False → True))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784306534677996773335400909940 : (((p3 ∨ (p1 ∧ ((((True ∧ p4) ∨ False) ∨ (False → p3)) → (True → (True → (p4 ∨ ((p5 ∨ p5) ∨ ((True → (p2 ∨ p3)) ∧ p2)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41564060664001430941597463068 : (((((p3 ∨ p3) ∧ (((p3 ∧ (False ∧ p2)) → p3) ∧ p3)) → (p1 ∧ (False ∨ (((p1 ∨ (True ∨ (True ∧ p2))) → p2) → p3)))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693924110316514628902951306000 : (((((((p2 ∧ False) ∨ p4) ∨ (p3 ∨ (p4 → (p2 ∨ p2)))) ∧ (True ∨ p4)) ∨ (((p5 → (p5 ∨ ((p4 → p4) → p4))) → False) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56405697465161310425485589351 : ((((p3 ∨ (p1 → False)) → False) → ((p2 ∧ (((p4 ∧ ((True ∧ (p3 → p3)) ∧ (p1 ∧ True))) ∨ (p4 → (True → p1))) ∨ p4)) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40966693625154758413661338944 : (((((p4 ∨ (p2 ∨ ((p3 ∧ False) ∧ p2))) ∧ (((p1 ∧ ((p4 → p4) ∨ (False ∧ p4))) ∨ (p4 ∧ p5)) → False)) ∨ (False ∧ False)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69113659891731580498928500141 : ((p5 → (((((((p3 ∧ ((p4 → (p1 ∧ p4)) ∨ p2)) ∧ p5) ∧ ((p4 ∧ p3) → p1)) → p1) ∨ (p1 ∧ True)) → False) ∨ (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719566724741554906923522272394 : ((((p4 ∨ ((p4 ∨ p5) ∧ False)) ∨ ((p4 ∨ (p2 ∨ (((True ∨ ((p4 ∧ p4) → p5)) ∨ (True ∧ p2)) → True))) ∨ (False ∨ (p5 → False)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148937846762660706223208289576 : (((p5 ∧ (True ∧ (False → p3))) → ((True ∨ p1) ∧ (p2 ∧ ((p4 ∧ p5) ∨ ((p1 → (p4 → p1)) ∧ p4))))) ∨ ((p3 ∧ False) → (p5 ∨ False))) := by
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
theorem thm_5_vars_200185063880097766945732604533 : (((p3 ∧ (p2 ∨ p5)) ∨ (True → (p4 ∧ p3))) → (p2 → (p1 ∨ (((p3 → (p2 → p2)) → ((p2 → (p4 ∧ (p1 → p3))) ∧ p2)) → p3)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119335192367498979920336798817 : ((p3 → ((p5 ∨ ((p3 ∨ p2) ∨ (True → p3))) → (p2 ∨ ((p4 ∨ ((((True → True) ∨ p5) → (p4 → p4)) ∨ p4)) ∧ True)))) ∨ (p2 → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119210980563840181094601997158 : ((p2 → ((p4 ∧ ((p1 ∨ p5) ∨ (p2 ∧ (p5 → (True ∨ p1))))) → (False ∧ (((False ∧ p4) ∧ p4) ∧ ((p4 ∧ True) ∧ True))))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350917487237676713816190300393 : (p4 → ((((((p5 ∨ p5) ∨ (((p1 → p4) → ((p1 ∨ p4) ∧ True)) ∧ False)) ∨ (p2 ∧ (p5 ∧ p5))) ∨ (False → p4)) ∨ p4) ∨ (p5 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58651937726232886685408320639 : (((p1 → p2) ∧ (p5 ∨ (False ∨ (((((False ∨ p2) → True) → p2) ∨ p3) → (p4 ∨ (p1 ∧ (((p2 ∧ True) ∨ p4) ∧ (True → False)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166225010774010021951630965323 : ((p2 ∧ (((p4 ∨ p1) → (((p2 → (p1 ∨ p1)) ∧ p2) ∧ True)) → ((p2 ∨ p3) → p4))) ∨ ((((p2 ∧ p4) ∨ (False ∨ p2)) → p2) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622561427751039565117261767135 : ((((p4 ∧ ((p2 → (((p5 ∨ (((p4 ∨ p1) → ((p2 ∨ True) ∧ p2)) ∨ False)) ∨ ((False → p5) → True)) → (True ∧ p1))) ∧ p2)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307860448815642314878810768708 : (p1 ∨ (p5 → ((((p2 → ((p3 ∨ p2) ∨ (True ∨ p4))) ∨ ((p5 ∨ False) ∨ ((p4 ∧ True) ∨ p3))) → (False ∧ (p1 → p1))) ∨ (p1 → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180639385114711853342724269657 : (((((p5 ∨ p4) ∨ (p2 ∧ p1)) → p3) ∨ (((p4 → p4) → p5) ∧ False)) → ((p3 ∨ (p5 → (p4 ∨ (True ∨ ((p2 ∧ False) ∧ p1))))) ∨ False)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692905788595979351400626942799 : (((((p2 ∨ p5) ∧ ((p2 ∨ ((p5 ∧ ((p5 ∨ p2) ∧ p2)) ∧ p1)) → False)) ∧ ((True ∨ p5) ∨ ((False ∨ p2) ∨ (p2 → (True → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208149216317670842543602686858 : ((((p5 ∨ p3) → True) → (p3 ∧ p4)) → (p5 → ((p3 ∧ (p3 ∧ (((((p2 → p4) ∨ (p2 ∨ False)) ∧ (False ∧ p2)) ∨ p4) ∨ p3))) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324182534746425063699690046512 : (p5 ∨ ((p3 ∨ (p2 → (((p2 ∧ p5) → (False ∨ p4)) ∧ False))) ∨ (p1 → (False → (((((p1 ∧ (False ∧ p4)) ∧ p3) → False) ∧ p1) → p3))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113505217572818833758860463607 : ((((((((p4 ∧ (p3 ∧ p5)) ∨ (p5 ∨ (p4 → p2))) ∧ p1) ∨ True) → p1) ∨ ((p2 ∨ (p1 → p4)) ∨ p5)) ∨ (p1 ∨ p2)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135358231830310320477379669974 : (((p5 ∨ ((p4 → (p2 ∨ p1)) ∨ ((p4 ∨ (((p5 → p1) ∧ (p1 → True)) ∧ p3)) ∨ p4))) ∧ ((p5 ∨ p1) → p5)) ∨ ((p5 → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327189802654005203505871836726 : (True → ((p3 ∨ ((True → (((True → p3) → (((False ∨ False) → (p4 → p4)) → (p3 → p3))) → ((False → (p4 ∨ p3)) → p5))) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325959806903134237117877011475 : (p5 ∨ (p5 ∨ (p1 ∨ ((p2 ∨ ((p1 ∨ ((p3 ∧ (p3 ∨ p5)) ∧ p4)) ∧ (p1 ∨ (p5 ∧ (True ∨ ((True ∨ p2) → p5)))))) ∨ (p4 → True))))) := by
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
theorem thm_5_vars_735548293996355338447021016398 : ((((p5 ∨ True) ∧ (((((p1 → p2) ∨ p5) ∨ (((p4 ∨ (p5 ∧ p5)) ∨ (p4 → p2)) ∨ p1)) ∧ ((p2 ∨ p3) ∨ (False ∨ False))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179374572771503555158009903580 : ((p2 ∨ (False ∨ (p5 ∧ ((p5 ∨ p5) ∧ (((p3 ∨ True) ∨ p5) → True))))) ∨ (((p2 → (((p2 ∨ p5) → p4) → (True ∧ p2))) ∨ p4) ∨ p1)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_473163623495120732135714332377 : (((((True → (((p2 ∨ p3) ∨ p5) → (True ∨ (True ∨ p5)))) → False) → ((False ∧ (((p5 → p3) ∨ (p2 ∧ (p2 → p1))) → p4)) ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True → (((p2 ∨ p3) ∨ p5) → (True ∨ (True ∨ p5)))) := by
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783075201955080678834330096502 : (((p3 ∨ ((((False ∧ p4) ∧ ((False ∧ p5) → (p2 ∧ (p5 → p2)))) ∨ (p4 → (p4 ∨ (p2 ∨ ((p3 ∧ False) ∧ True))))) → (p1 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613905169930676707573383606559 : (((((((p2 ∨ p3) → ((((p5 → False) ∧ (p5 ∧ (p2 ∨ ((p4 ∨ p1) ∨ True)))) ∨ p4) ∨ p5)) → p5) ∨ (p3 ∧ (True ∨ True))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259339252645487353863541431541 : ((False → p2) → (((p3 → (p5 → True)) → False) → (((((((True ∧ ((p5 ∧ p4) ∨ p1)) → p1) ∨ (p1 → False)) ∧ p1) → True) → p3) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (p5 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h4
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p3 → (p5 → True)) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h8
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51978535772387674792558803783 : ((((p2 ∨ p1) ∧ ((True → (p4 → ((p5 ∧ ((p5 → p4) ∨ True)) → p5))) ∧ p5)) ∨ (((p4 ∨ (p1 ∧ (p3 ∧ False))) ∨ p3) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177660303644626212603227213508 : ((((False ∧ (((p3 → (p1 → (p5 ∧ p5))) ∧ True) → p2)) ∨ p2) ∧ p1) ∨ ((((p2 ∧ p4) ∧ p3) ∨ p4) ∨ ((p2 ∧ (p4 ∧ p2)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111284171880980056617982849998 : ((((True → p1) → (p4 → ((((True → (True → p5)) → False) → True) ∧ ((p5 ∧ (((False ∨ p5) ∧ p2) ∧ p5)) ∧ p2)))) ∧ False) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119269676469351887614627008727 : ((p3 → (((p4 ∧ (False ∧ (False ∨ ((False ∨ p5) ∨ ((p1 ∧ (False → (True ∨ ((p2 ∨ True) ∧ p5)))) ∧ p3))))) ∧ p5) ∧ p1)) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46839692042471785543112671029 : (((((p2 → ((p5 ∨ p4) ∨ ((True → False) → p5))) ∨ (p2 → ((p2 ∧ (True ∧ (p2 → (p2 ∨ p4)))) ∧ False))) ∧ p2) ∨ (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180222818349854984367828222471 : ((((p3 → p1) → ((((True → p4) ∧ p5) ∨ p5) ∧ (p2 ∨ True))) → False) → ((p5 ∨ False) ∨ ((((p5 ∧ p4) ∧ True) → (True → p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : ((p3 → p1) → ((((True → p4) ∧ p5) ∨ p5) ∧ (p2 ∨ True))) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328095273740022679244974059170 : (True → (((p1 ∨ (p1 ∧ (p2 ∨ ((p2 ∨ p5) ∧ (((p2 ∨ (p4 ∧ p4)) → p3) ∨ (p2 → (p4 ∨ p1))))))) ∧ p1) ∨ (p4 → (True ∨ p2)))) := by
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
theorem thm_5_vars_166403705342506257313046002204 : ((False ∨ (p1 → ((True ∧ ((p2 ∨ p3) ∨ ((p3 → p4) ∧ p5))) ∨ ((p1 ∧ p2) ∨ p1)))) ∨ ((True → (p3 ∨ (p4 → True))) → (p3 ∨ False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66661752967656555240077515235 : ((True → ((p3 ∧ ((((p3 ∨ True) ∧ p4) ∧ p3) → p5)) → ((True ∧ p5) ∨ ((True → (p5 → (p3 → ((p4 ∨ True) ∧ p2)))) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748713624010116578345070701792 : ((((p3 → p4) → (((p2 ∧ (p2 ∨ p3)) → (((False ∨ False) → p2) ∧ p4)) → ((p4 ∧ p4) → ((p4 → p3) → (p3 ∨ (p3 ∨ p4)))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50476368103830250051205840487 : (((p1 → ((p4 ∨ p3) ∧ ((p4 ∨ (p2 → True)) → ((p2 → (True → ((p3 ∨ False) ∨ False))) ∧ False)))) ∨ (((True ∨ p4) → p2) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353522999614473887014723345285 : (p4 → (p2 ∨ (p3 → ((p3 ∧ ((p4 → ((((p5 ∨ True) ∨ ((p4 ∨ p1) → p5)) → ((p2 ∧ p3) → (p3 ∧ False))) ∨ p4)) ∧ p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336119004266865495357488060025 : (p1 → ((((((((False → p5) → (p3 ∨ False)) ∧ ((p1 ∧ True) ∨ ((p4 ∨ p5) → p5))) → p4) ∧ p2) ∧ (False → (p2 ∨ False))) ∨ p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319105075925504144546412892735 : (p4 ∨ ((p2 ∧ (((p1 ∨ True) → (((False ∧ p5) ∨ p2) → (p2 ∧ (p5 ∧ (p2 → True))))) ∧ (True ∨ p3))) → ((p2 → (p3 ∨ p3)) ∨ p5))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : (p1 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((False ∧ p5) ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h14
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336224123400583968585138026438 : (p1 → (((((((p2 ∨ (((p2 ∧ p5) ∨ p2) → p4)) → (p5 → (p2 ∨ (p3 ∨ p1)))) ∨ p3) ∨ True) → p5) ∨ (False → (p1 ∧ p3))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256468486646842414455398481893 : ((False ∨ p4) → ((False ∧ (p2 ∧ (p1 → ((True ∧ ((p1 ∧ (p3 ∨ (p4 → ((p2 ∨ (False ∨ p5)) → p5)))) ∨ False)) ∨ False)))) ∨ (False ∨ p4))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157776106395246635879577002839 : (((((False ∨ p3) ∧ (p5 → (p4 ∨ (p3 ∧ (False ∨ p1))))) ∨ p4) ∨ (((p4 → True) → True) ∧ p5)) ∨ (True ∨ (p5 ∨ ((True ∨ p2) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164918536416295191192785190974 : (((((((True ∨ False) ∧ p3) → ((p3 → ((p3 ∧ p5) ∨ p1)) ∧ p4)) ∧ p2) ∨ p5) → False) ∨ ((((False ∧ p1) ∨ (True → p2)) ∧ p1) → p2)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320285595719975225820315913201 : (p4 ∨ ((p3 ∧ p3) ∨ ((p4 ∨ (True ∧ ((((((p3 ∨ p4) → p1) → p5) → (p5 → ((p5 ∧ p5) ∨ p2))) → (p3 ∧ p5)) → p5))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p3 ∨ p4) → p1) → p5) → (p5 → ((p5 ∧ p5) ∨ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616019790029750183445727235982 : (((((((p4 ∨ p4) ∨ p3) ∧ ((p3 ∨ p4) → ((p1 ∨ p2) ∧ (p3 ∨ p2)))) → ((p2 → ((p1 ∧ True) ∨ (p4 → p5))) ∨ p2)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175189381080669138831062745250 : ((False ∨ ((p3 ∨ (False → (True → ((True → (p4 ∨ p3)) ∧ (p3 ∨ p5))))) ∧ p3)) → ((((((p5 ∧ p5) ∨ False) ∨ p2) ∧ True) ∨ False) ∨ p3)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64571338050901403287053078191 : ((p1 ∨ ((p4 ∧ (p2 ∧ p1)) ∨ (((((p3 ∧ p2) ∧ False) ∧ ((p1 ∨ p4) → (p1 → p3))) ∧ ((False ∨ p2) ∧ (p4 ∨ False))) ∨ True))) ∨ p5) := by
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
theorem thm_5_vars_326905201819230654450825112349 : (True → ((((False → ((p1 ∨ (p3 → p5)) ∧ (p1 → ((p5 ∨ ((p1 ∨ (True → (p2 ∨ False))) ∨ p3)) ∧ (True → p1))))) ∨ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800311439373093671692309592532 : (((p2 → (((False ∧ (((p3 ∨ ((p5 ∨ (p3 ∧ p5)) ∧ (p2 ∧ False))) ∨ p1) ∨ False)) ∨ ((True ∧ (p1 ∨ False)) ∨ (p4 ∧ p4))) ∨ True)) ∨ False) ∧ True) := by
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



