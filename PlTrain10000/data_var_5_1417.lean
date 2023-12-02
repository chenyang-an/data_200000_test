variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51666884224383153741710649829 : (((((p4 ∨ False) ∨ ((p2 → False) ∧ ((p3 ∨ p3) → ((p2 → False) ∨ p2)))) → p4) ∧ ((True → False) ∧ (False ∧ ((True ∨ p2) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346798527171942811944540243763 : (p3 → ((p5 ∧ ((p5 ∨ (p2 → ((p4 ∧ (p2 → False)) → ((p2 ∧ True) → (p3 → (False → p2)))))) → p1)) ∨ (((p4 ∧ p4) → p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683062055423075653011960735854 : ((((False ∧ ((p5 ∨ (False ∧ ((p3 ∧ False) → p5))) ∧ ((True → p1) ∧ (p2 → (p1 → p3))))) ∧ (p4 ∨ ((p3 ∧ p1) → (p1 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303922129693649365590457006556 : (p1 ∨ (((False ∨ ((p5 ∨ ((p1 ∧ (False ∨ p2)) ∧ p5)) ∧ p1)) ∨ ((p2 ∨ True) ∨ ((p5 → False) ∨ ((p3 ∧ True) → (False ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256597772494899835814443715936 : ((p1 ∨ True) → (((True ∧ (((p1 ∧ False) ∨ (p3 ∨ False)) ∧ p4)) ∨ ((True ∧ (False ∨ p2)) ∨ False)) → (((p5 → p3) ∨ (p4 ∧ p1)) ∨ p2))) := by
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
        cases h1
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h7
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204941364215017664737669872863 : ((((p2 ∨ p5) → (p1 ∧ p1)) → p2) ∨ (((True ∧ p1) → (False ∨ (True ∨ p4))) ∧ ((((p1 ∧ p1) → p1) ∧ True) ∨ ((p3 → False) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53379945420475786048900584292 : ((((((p3 ∨ (p4 ∨ p1)) ∧ True) ∧ ((p1 → p1) ∧ p4)) → p3) → ((((p3 ∧ False) → (False ∨ ((p5 ∨ p5) → p5))) ∧ False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337552318353620425915419807295 : (p1 → ((p5 ∧ ((((((p4 ∧ p5) → p2) ∨ ((p2 ∧ p5) → (True ∨ p1))) → (False ∧ p3)) ∧ p5) ∨ p2)) ∨ (((True → False) ∨ True) ∨ p5))) := by
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
theorem thm_5_vars_41398595330861185665412120565 : ((((p2 ∨ (((False → ((p2 ∨ (p5 → p3)) → False)) → p5) ∧ (True → p3))) ∧ (((p5 ∨ (False → p2)) ∨ False) ∨ (p5 ∨ p5))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258543556426426554583118737209 : ((p5 ∨ p3) → ((p2 ∨ ((p2 ∨ p2) → ((False → (True → p2)) ∧ (p3 ∨ False)))) ∨ (p5 ∧ (((p2 → (p3 ∨ p5)) ∧ True) ∨ (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347531877546303995346435972967 : (p3 → ((p5 ∧ (((p2 → p5) ∧ True) ∧ p2)) → ((False ∨ ((p4 ∨ p2) → ((((False → False) ∧ p1) → p3) ∧ (False ∨ (False ∨ p3))))) ∨ p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52080982508019778634444317747 : ((((p2 ∨ ((((p2 ∧ False) → (((True ∨ p1) ∨ p5) ∧ p1)) → p1) → True)) ∧ True) → ((p2 ∧ (p4 ∨ True)) → (p1 ∧ (p3 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_667565330902111121363372368124 : ((((p1 ∧ ((p3 → (p4 ∨ (p2 ∨ (((p1 → (p2 ∨ p3)) ∨ False) ∧ p2)))) ∨ ((p3 → (p3 ∧ p2)) → p5))) ∧ ((p4 → p5) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_74089645650890288752782542489 : (((((True ∨ p1) ∧ (False → p5)) ∧ ((((True ∨ ((((p3 → p2) ∧ ((p1 ∨ p5) → p5)) → p2) ∧ p2)) → False) ∨ True) → p3)) ∨ p3) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : (((True ∨ ((((p3 → p2) ∧ ((p1 ∨ p5) → p5)) → p2) ∧ p2)) → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h11 : (((True ∨ ((((p3 → p2) ∧ ((p1 ∨ p5) → p5)) → p2) ∧ p2)) → False) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h11
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597780400673797531328460246848 : (((((p2 → (p2 → (p3 → p3))) → ((p4 ∧ (((((p1 ∧ p2) ∧ p5) → False) ∨ (p3 ∧ (p3 ∧ p2))) ∨ False)) ∨ (p5 ∨ True))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138550623928696943528905936333 : ((((p2 ∨ ((p5 ∨ p4) ∧ ((True ∨ (p4 ∨ p4)) ∧ (p2 ∧ (((p4 ∧ True) ∧ p5) ∨ (False ∧ p3)))))) ∨ p3) ∧ p2) → (False ∨ (p1 ∨ p2))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h11.left
          let h14 := h11.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Conjunctions on the left can always be decomposed.
            let h18 := h16.left
            let h19 := h16.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- False on the left can always be used.
            apply False.elim h21
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- Conjunctions on the left can always be decomposed.
            let h25 := h11.left
            let h26 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h26
            case inl h27 =>
              -- Conjunctions on the left can always be decomposed.
              let h28 := h27.left
              let h29 := h27.right
              -- Conjunctions on the left can always be decomposed.
              let h30 := h28.left
              let h31 := h28.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h32 =>
              -- Conjunctions on the left can always be decomposed.
              let h33 := h32.left
              let h34 := h32.right
              -- False on the left can always be used.
              apply False.elim h33
          case inr h35 =>
            -- Conjunctions on the left can always be decomposed.
            let h36 := h11.left
            let h37 := h11.right
            -- Disjunctions on the left can always be decomposed.
            cases h37
            case inl h38 =>
              -- Conjunctions on the left can always be decomposed.
              let h39 := h38.left
              let h40 := h38.right
              -- Conjunctions on the left can always be decomposed.
              let h41 := h39.left
              let h42 := h39.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h43 =>
              -- Conjunctions on the left can always be decomposed.
              let h44 := h43.left
              let h45 := h43.right
              -- False on the left can always be used.
              apply False.elim h44
      case inr h46 =>
        -- Conjunctions on the left can always be decomposed.
        let h47 := h8.left
        let h48 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h47
        case inl h49 =>
          -- Conjunctions on the left can always be decomposed.
          let h50 := h48.left
          let h51 := h48.right
          -- Disjunctions on the left can always be decomposed.
          cases h51
          case inl h52 =>
            -- Conjunctions on the left can always be decomposed.
            let h53 := h52.left
            let h54 := h52.right
            -- Conjunctions on the left can always be decomposed.
            let h55 := h53.left
            let h56 := h53.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h3
          case inr h57 =>
            -- Conjunctions on the left can always be decomposed.
            let h58 := h57.left
            let h59 := h57.right
            -- False on the left can always be used.
            apply False.elim h58
        case inr h60 =>
          -- Disjunctions on the left can always be decomposed.
          cases h60
          case inl h61 =>
            -- Conjunctions on the left can always be decomposed.
            let h62 := h48.left
            let h63 := h48.right
            -- Disjunctions on the left can always be decomposed.
            cases h63
            case inl h64 =>
              -- Conjunctions on the left can always be decomposed.
              let h65 := h64.left
              let h66 := h64.right
              -- Conjunctions on the left can always be decomposed.
              let h67 := h65.left
              let h68 := h65.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h69 =>
              -- Conjunctions on the left can always be decomposed.
              let h70 := h69.left
              let h71 := h69.right
              -- False on the left can always be used.
              apply False.elim h70
          case inr h72 =>
            -- Conjunctions on the left can always be decomposed.
            let h73 := h48.left
            let h74 := h48.right
            -- Disjunctions on the left can always be decomposed.
            cases h74
            case inl h75 =>
              -- Conjunctions on the left can always be decomposed.
              let h76 := h75.left
              let h77 := h75.right
              -- Conjunctions on the left can always be decomposed.
              let h78 := h76.left
              let h79 := h76.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h3
            case inr h80 =>
              -- Conjunctions on the left can always be decomposed.
              let h81 := h80.left
              let h82 := h80.right
              -- False on the left can always be used.
              apply False.elim h81
  case inr h83 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137504623409933525907152824221 : ((p5 ∧ ((p3 ∨ (p3 ∧ (((p1 ∨ ((p2 ∨ (p3 → True)) ∧ p3)) ∧ True) ∧ (p1 ∧ p4)))) → (p2 ∧ (p5 → p3)))) ∨ (False → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595363784171542109327449531105 : (((((False ∧ ((p5 ∨ ((p1 ∧ (p1 ∧ p1)) ∧ p4)) ∨ (True ∧ p3))) ∧ (((False ∨ p1) ∧ ((p4 → (True ∧ p5)) ∨ True)) → p5)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158080245715332695112434965404 : ((((p1 ∨ p3) ∨ (True ∧ (p2 ∧ p2))) → (p2 ∨ (False ∧ ((p1 ∨ ((p1 ∨ p1) ∧ p3)) ∨ p5)))) ∨ (False → ((True → (p2 ∧ p2)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610894045804774250429906648149 : ((((((True ∧ (((p1 ∨ (p4 → True)) → ((False ∨ p4) ∨ p5)) ∧ p5)) ∨ (p2 → (((p1 ∨ p2) ∧ (p5 → p4)) → True))) → False) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174274622489039465611486328387 : ((((p3 ∧ (p2 ∨ p2)) ∨ (p4 ∧ (p5 → (p5 ∨ p5)))) ∧ (True ∧ (p4 ∨ p1))) → ((False ∨ True) ∨ ((False → True) ∧ (p2 ∧ (p4 ∧ p4))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664939024507581809001573110057 : ((((p3 → (((p4 ∨ (((p4 ∨ True) → p1) → True)) → ((True ∧ p4) ∨ False)) → (((p3 ∧ p5) → True) ∨ (p5 → p2)))) → (p5 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158523650519254500508312250033 : (((p4 ∨ p3) → ((p5 ∧ (p3 ∨ p2)) ∨ ((((p5 ∧ (p1 ∧ p4)) ∨ p2) ∨ p1) ∧ (p4 ∧ p5)))) ∨ (((p1 ∧ (p2 ∧ p5)) → p5) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60762527849600666474719510124 : ((True ∧ ((p1 → p1) ∧ ((((((False ∧ (True ∧ p2)) ∧ p2) ∨ False) ∨ p2) ∨ (p3 → True)) ∧ ((p1 → (p3 → (p1 ∨ p4))) ∨ p3)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213856926116154435913626337199 : (((False ∨ (p4 ∨ p5)) ∨ p1) ∨ ((((p5 → False) ∨ p3) ∧ (p1 ∧ p3)) → (((p1 ∧ (p4 ∧ (p3 → p4))) → ((p3 ∧ p1) ∧ p5)) ∨ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133791715282698621260491251377 : (((((p3 ∧ p4) ∨ p2) ∨ ((p2 ∧ (((p1 ∨ p1) ∧ p2) ∨ p2)) ∨ ((p5 → ((True ∨ True) → True)) ∧ p5))) ∧ p4) ∨ (p2 ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47541729033874823463219783375 : (((p5 ∨ (((((p4 → ((p2 ∨ ((p3 ∨ False) ∧ p4)) → p2)) → p2) → (False ∨ p3)) → (p3 ∨ p5)) ∨ (p2 ∧ p1))) ∨ (False → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46062032009874682201584973587 : ((((((p4 ∧ (p3 → True)) ∨ ((((p1 ∧ (False ∨ p3)) ∨ p4) → (p5 ∨ (p5 → (p1 ∧ p3)))) ∨ True)) ∨ p5) ∨ False) ∧ (p2 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738522129763547834733185182760 : ((((p1 ∧ p4) ∨ (((False ∨ p5) ∨ (True ∨ p2)) → (((p2 ∨ p3) → p2) → (False ∨ (((False → ((p3 ∧ True) ∧ p2)) → p5) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135456662724502329174739659787 : ((((((p4 → (False ∨ (((p1 → ((p3 ∨ False) ∧ p3)) → False) ∨ p4))) → p1) → p4) → False) → (p5 ∧ (True → p4))) ∨ ((p5 ∨ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118289550302861078936621586357 : ((p1 ∨ ((p2 ∨ p2) → ((p1 → (p1 ∧ (p2 ∧ p5))) → (p4 ∧ ((False ∧ ((p3 ∧ p1) → ((p2 ∧ p2) ∨ p3))) ∧ p5))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721169418620550266645378648142 : (((((p5 → True) ∨ (p5 → False)) → ((((((p3 ∨ p4) → p3) ∧ (p2 ∨ p4)) ∧ ((p4 ∧ ((p2 ∧ p5) ∨ p1)) ∨ p1)) ∨ p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47392820855056326542411025185 : ((((p3 → p5) → (p1 ∧ (((p3 ∨ False) → ((p4 ∧ p3) ∨ (p2 → (p2 → p4)))) ∨ (p1 ∧ ((p3 ∨ True) ∧ p3))))) ∨ (p3 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622393176442398770491608833895 : ((((p3 ∧ ((p2 ∧ ((p2 ∨ (p4 → (p1 ∨ p5))) ∨ (p4 → (p2 ∨ False)))) ∨ ((p1 → (p4 ∧ p4)) → ((False ∧ p2) ∨ p5)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112636027099544527322501773466 : (((((((True → True) → p3) ∧ False) ∧ (p1 ∧ (((p4 ∧ (p5 ∧ p5)) ∨ p5) → (False ∧ (p5 ∨ p1))))) → (False ∨ p4)) → p2) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158631544547070193258397018930 : ((p1 ∧ ((p1 ∨ (p2 → (p1 → ((p2 ∧ ((False ∧ False) ∧ p1)) ∨ (True ∧ (p1 ∧ p4)))))) ∧ p1)) ∨ (((p4 ∧ (p1 ∧ p1)) ∨ False) → p4)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110708442899220842595049940805 : (((((False ∧ ((p1 ∨ (((p3 → (p5 ∧ p4)) → (p5 ∧ (p1 → False))) ∨ p3)) ∧ ((p4 ∨ True) ∨ True))) ∨ False) ∧ p4) ∧ False) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587666851972547448802899929437 : (((((((p4 → ((p3 ∧ (p4 ∧ (p5 → p1))) ∧ p1)) ∨ (((p5 ∧ (p4 → ((p2 ∧ p2) ∧ p3))) ∨ True) ∧ p1)) → p3) ∨ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178172132384715955072020834253 : ((((p1 ∨ True) → (p3 → (((True → (p2 ∧ p1)) ∨ p4) ∧ True))) → False) ∨ (((p4 ∧ (p3 ∧ p5)) ∨ (False ∧ (p4 ∧ (True → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111882697110392810859772221252 : ((((p4 ∨ (p1 ∨ (p5 ∨ (p1 → (p4 ∧ ((p4 ∧ ((p1 → False) ∨ p3)) ∨ p1)))))) → (((False ∨ p4) → p5) ∧ p3)) ∨ p3) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51060916966443432966234332841 : (((True → ((p4 ∨ (((p4 ∨ p3) ∧ p5) ∧ (p1 → p3))) → (((p4 → p1) ∨ p3) ∧ p4))) ∧ ((p4 ∧ False) ∨ (True ∨ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114120240595653795641476564268 : (((True → ((True → (p5 ∨ p1)) ∨ (p4 ∨ ((((p3 → (True ∨ p2)) ∧ p4) ∨ (p3 → p2)) ∨ p4)))) ∨ ((p4 ∨ p2) ∧ p4)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58867981532353973968826371286 : (((False ∧ True) ∨ (((p1 → p3) → (((False ∨ ((p4 ∨ p3) → True)) → p3) ∨ (True → (((p3 ∨ True) ∨ p2) ∨ True)))) ∨ (p3 ∧ p1))) ∨ p3) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697490829214341103376041642784 : ((((p3 ∧ (p1 ∧ (((((False → p3) ∨ p3) → p1) ∨ True) ∨ p1))) ∧ (((False → p3) → p1) ∨ (((False → p1) → p1) ∨ (p4 ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44146533131758309756948442243 : (((((False → (((False → p5) ∨ p2) → (p5 ∨ (False → (p2 → (False ∧ ((True ∧ p1) ∨ p5))))))) ∧ p4) → ((p1 ∧ p4) → p4)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261495391856370651170583466949 : ((p5 → p3) → (((((p5 ∧ True) → p4) → (((False → (p2 ∨ ((p1 ∨ True) ∧ p1))) ∧ True) → ((False → (False → p5)) ∧ False))) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739521404504765911113533949711 : ((((p5 ∧ p1) ∨ (p4 → ((p2 → ((False → (((((False ∨ (p1 ∨ False)) ∧ p1) ∧ p4) ∧ False) → (p1 → True))) ∨ (p1 ∨ p1))) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200863610540031698937177001128 : ((True ∨ (p5 ∨ ((False ∧ (False ∧ p1)) → True))) → ((p5 ∨ (p1 ∨ p1)) ∨ (((False ∨ (False → (p5 → True))) ∨ ((p3 ∧ True) ∨ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329306011951169898319717124366 : (True → ((p3 ∨ (False ∧ p3)) ∨ (p3 ∨ ((False ∨ (((p1 → (p2 ∨ (p2 ∧ False))) → (p5 ∨ (False ∨ True))) ∧ True)) ∨ (False → (p1 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215890984031993625814332505031 : ((p3 ∨ ((p2 ∧ p3) ∨ False)) ∨ ((p4 ∨ (((p1 ∨ ((False → p5) ∨ p3)) → (True ∨ p1)) ∨ p2)) ∨ (p3 ∧ ((p3 ∧ True) ∧ (False → False))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114812348926810577010515036207 : ((((p3 → True) ∧ (((((p2 → True) ∧ True) ∧ (p2 ∨ False)) ∨ True) ∨ p5)) ∧ ((p1 ∨ ((p5 ∧ p4) ∨ (True ∨ p3))) ∨ p5)) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_653470278805789948433184169055 : ((((p4 → (p5 ∧ (p5 → (((p2 ∧ (p3 → False)) ∧ (p2 ∧ p3)) ∨ (((p5 → False) ∨ (True ∧ p4)) ∧ (p1 ∧ True)))))) ∧ (p1 → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323514248712064550137149486504 : (p5 ∨ (((p4 → p1) → (((True → (p5 ∨ (((False ∨ (False ∧ False)) → True) ∧ (p3 ∧ p2)))) ∧ p2) ∨ (True → p3))) ∨ ((False → p2) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157543566498488345105068281324 : (((((((False ∨ False) ∧ ((p1 ∧ p3) → ((True → p2) ∨ p5))) ∨ True) ∨ True) → p3) → (p3 ∨ p4)) ∨ ((((False ∨ p5) ∨ p4) ∧ False) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False ∨ False) ∧ ((p1 ∧ p3) → ((True → p2) ∨ p5))) ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313139445688564643728285640107 : (p3 ∨ ((((p4 ∨ p2) ∨ (((((p2 ∨ (p5 ∧ (p5 ∧ p5))) ∧ p4) ∨ p3) → p5) ∨ True)) ∨ (((p3 → p3) ∨ (p5 ∧ p4)) ∧ p4)) ∨ p4)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778245791493108110542023067631 : (((p1 ∨ ((p3 → p3) → ((p5 → p1) ∨ ((p1 → ((True → ((p3 → p1) ∧ p4)) ∧ p2)) ∨ ((True → (True → (p2 → True))) ∧ True))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52747036688644572266225111288 : ((((p5 ∧ (False ∨ (p4 ∧ (p1 → ((p2 → p3) ∧ (p1 ∨ p1)))))) ∨ True) → (((True → (((p5 → p2) → p3) ∧ False)) ∨ p4) ∨ True)) ∨ p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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
theorem thm_5_vars_148028971374229161258539523343 : ((((False → ((True ∨ True) → p3)) → ((True ∧ False) ∨ (p1 ∧ ((p3 → p1) ∧ (p5 → p5))))) ∨ (p1 → p1)) ∨ ((False ∧ (p4 ∨ p3)) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115830980882335897899001186976 : ((((p1 → p3) → (p3 → False)) ∧ (((((False ∧ True) ∧ p4) ∨ p3) ∧ p2) ∨ (((p1 ∨ p4) ∧ ((p5 → p1) → p3)) → False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45406722273129187829701194058 : (((p5 ∧ ((False → (True → p3)) ∧ (p4 → (True ∨ (p1 → (p4 ∧ ((p4 → (p2 ∨ p4)) ∧ ((p2 ∧ p2) ∧ (p4 → p4))))))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356540729065946594025391295424 : (p5 → ((p4 ∧ (((p1 → ((True → True) ∧ True)) → False) ∧ p5)) ∨ ((((False ∧ p2) ∨ (p1 → ((p4 ∧ p2) ∧ (p1 ∨ p5)))) ∨ p4) → p5))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38427925155670149808766484343 : (((((p3 ∧ ((p2 ∨ ((False ∧ p3) ∨ (p3 → p4))) ∨ (p4 ∨ p1))) ∧ p5) ∨ (False ∧ (False → (p2 ∨ ((p4 ∨ p4) → p1))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134121922967870850380742835579 : (((((p3 → (((((p1 → True) ∨ p2) → p2) ∧ p2) ∧ p4)) → (((p5 ∨ p5) ∧ p5) → p2)) ∨ (p4 ∧ p5)) ∨ p5) ∨ ((p1 ∧ False) → p5)) := by
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
theorem thm_5_vars_41371959897967071025204331171 : (((((p3 ∨ p2) → (True → (((((p2 → p3) ∨ (p1 → p1)) → p4) ∨ p5) ∨ p5))) → ((p2 → (p3 ∧ (p5 ∨ p3))) ∨ False)) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198466713087461953556232708877 : ((p5 ∧ (p4 ∧ (p2 ∨ ((False → p1) ∨ p3)))) ∨ ((((p5 ∧ (p3 → (p1 → p5))) ∧ (p4 ∨ p5)) ∧ ((p2 → True) → p1)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337875082918174501297673694803 : (p1 → ((True → (((p5 → (p4 ∧ ((False ∧ True) ∧ False))) ∧ (p2 ∨ p4)) ∨ p3)) ∨ (p4 → ((p4 ∧ (False ∨ p1)) ∨ ((True ∨ False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56687528395150668131484996712 : ((((p5 → p3) ∧ p4) ∧ (p1 → (p5 → (((((p3 → (((p5 ∧ (p4 ∨ True)) ∧ p5) ∧ p5)) → True) ∧ (True → p2)) ∨ p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150067540916303671981742325240 : ((True → (((p4 → True) → (((p4 → p3) ∨ (p3 ∧ p4)) ∨ p4)) ∨ (False → (p4 ∧ ((True → False) ∧ p4))))) ∨ ((p5 → (p2 → p4)) ∨ False)) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44392914621027825544990655056 : (((((True ∨ p5) → ((p5 → ((True → p1) ∨ (True ∨ p1))) ∧ (p3 ∧ p1))) ∨ (p4 → ((((True ∨ p2) → p4) → p4) ∨ True))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118242324658477724648564267890 : ((p1 ∨ ((((((False ∨ (p2 ∨ p1)) ∧ (p5 → ((((p2 → p3) ∧ False) → p4) ∧ p4))) ∨ p1) → p4) ∧ True) ∨ (True → p1))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46663417050398838133605832090 : (((False ∨ (((p4 ∧ p5) → p2) → ((((p1 → False) ∨ p1) ∨ ((p2 → (p4 ∧ (p4 ∧ p2))) ∨ p1)) ∧ (True → p3)))) ∧ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178643594223931288636166834362 : (((p4 ∨ ((True ∨ p3) ∧ (p3 ∧ p4))) → ((p1 → (True → p1)) → False)) ∨ (((p4 ∧ (False ∨ (p3 ∧ (p3 ∧ (p4 ∨ p1))))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53103756961357323958613048690 : (((True → ((p4 ∧ (p3 → (False ∨ ((p3 ∨ True) ∧ p2)))) ∨ True)) ∧ (((p4 → p5) ∧ p3) ∨ (p5 ∨ (p2 → (False ∨ (p2 → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116440338754006746691526174301 : (((p3 → (p3 ∧ p4)) → ((True ∨ (((p4 ∧ p2) ∧ p2) → True)) → (p3 ∨ ((((p5 ∨ (p4 → False)) ∨ True) ∨ p4) → p2)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113724758334592848961827887753 : ((((((p1 ∨ p1) → p2) ∨ ((p3 ∨ (p3 ∧ p4)) → ((p1 → (p1 → False)) ∨ p5))) ∧ ((p5 ∨ True) ∨ p1)) → (p4 ∨ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190483291126535128513232797191 : ((((p1 → (((p5 ∧ p3) ∧ p5) → p1)) ∧ p1) → p3) ∨ (True → (p4 ∨ ((((p3 → p5) ∨ True) ∨ p5) ∨ ((True → (False ∧ False)) ∨ p2))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616858734394362042763851627859 : (((((((p2 ∨ ((p5 ∧ p2) ∧ (False → p3))) ∨ p1) → p2) → (((p2 ∧ ((True ∨ p3) → p5)) ∧ p1) ∨ ((p3 ∨ p3) ∨ p2))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190295847803323453142725354334 : (((((p1 → (p1 ∨ p1)) → (p5 ∧ p3)) → False) ∨ p1) ∨ ((p2 → ((False ∨ (p2 ∨ p3)) → p3)) → (p4 ∨ (p3 ∨ (True ∨ (False ∨ p4)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218763034325098742130697886101 : ((p1 ∧ ((p1 → True) ∧ True)) → (((p3 → p3) → ((p5 ∧ p5) ∨ (p1 → (p2 ∧ (((p1 ∧ (p1 ∧ (p5 ∨ True))) ∧ p1) ∧ False))))) ∨ p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299127040828138699688287434505 : (False ∨ ((((p4 ∧ ((True ∧ ((p5 ∨ ((((p2 ∨ True) ∧ ((False ∨ False) → p4)) ∧ p2) ∨ p1)) → (False ∨ p4))) ∨ p3)) ∨ False) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135548853590995996867197279007 : ((((True ∧ p5) ∧ (p4 → (True → ((p3 → p2) ∨ ((p3 → (p1 ∧ True)) ∨ p5))))) ∧ (((p3 ∨ False) → p4) ∨ p5)) ∨ ((p1 ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342408125641576233002667230568 : (p2 → ((p4 → (p2 → (((((((p4 ∨ p1) ∨ p3) → p3) ∨ False) → p3) ∨ True) → p3))) ∨ ((p1 → ((True ∨ (p2 → p2)) ∧ p2)) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629513986576226247330636435025 : ((((((p3 → (((p4 ∨ p4) ∧ (((((p5 ∧ (False ∧ p1)) ∨ p4) → (p4 ∨ p2)) ∨ True) ∨ p5)) ∧ p4)) ∨ (p2 ∧ False)) ∨ p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64788098336154502316375507286 : ((p2 ∨ (((((p1 → (p5 ∨ p3)) → (p4 ∧ ((True ∨ False) ∧ True))) ∧ (p2 ∨ p3)) ∨ (p2 ∧ (p4 ∧ (p2 ∨ (p1 → False))))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304774027645656335795409901399 : (p1 ∨ ((p2 ∨ ((p1 ∨ ((((p1 ∧ p3) ∧ p4) → p4) → p3)) ∧ (True ∧ (False → (((p5 ∧ (p1 → p5)) ∨ p4) ∨ False))))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612874948135043084821598501345 : (((((p5 ∧ ((p2 → (p1 ∧ ((False → (((p4 ∧ p5) ∧ False) → (False ∧ p2))) → (False ∨ False)))) ∨ (p3 → p5))) ∨ (p1 → p2)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_322594045730156095921275329145 : (p5 ∨ ((p1 → ((((((p1 ∧ (((p5 ∨ ((False ∨ (p2 ∧ p1)) → p5)) ∧ True) ∨ p1)) → p3) ∨ p4) ∨ p1) → (p4 ∧ p3)) ∨ p1)) ∨ p2)) := by
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
theorem thm_5_vars_215349783309297589931543878099 : ((p2 ∧ ((False ∧ p1) ∧ p4)) ∨ ((p2 ∧ (((True ∧ p2) ∧ ((p1 → p1) ∨ True)) → p1)) → ((p4 ∧ (False → ((p4 → True) ∨ p4))) ∨ p2))) := by
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
theorem thm_5_vars_1997077473347625240307802187 : (((((p4 → p3) ∨ p2) → ((p3 ∧ ((p4 → p5) ∧ ((p1 ∨ p3) → False))) ∧ p2)) ∧ (True → p3)) → ((p1 ∧ p1) ∨ (p1 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 → p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h6
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : (p1 ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h13
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h15 := h11 h12
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310346022448272967516771547394 : (p2 ∨ ((p2 → (p1 ∧ (p1 → (False → ((p2 ∨ False) ∨ False))))) → (p4 → ((((p3 ∨ p2) ∨ (p1 ∨ ((False ∧ False) ∧ p5))) ∨ True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156867649749708805875650930111 : (((((False ∨ (p3 ∨ p4)) ∧ (((False → (True → p3)) → (p4 ∨ (p1 ∨ True))) → p3)) ∧ False) ∨ True) ∨ (p3 ∨ ((p1 → (p4 → p4)) → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698000842259601406297957666796 : ((((((((p1 → (p1 ∨ p3)) ∨ p4) ∧ (p1 ∨ p5)) ∨ p3) ∨ p4) ∨ (True → ((p5 ∨ ((p1 ∨ p1) → (p5 ∧ (True ∨ p4)))) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135403387567870381902899492929 : ((((((False ∧ p1) ∨ (True → p1)) ∨ p3) ∧ (((p4 → (p1 → p1)) ∨ False) ∧ (p1 ∧ True))) ∨ (p3 → (p2 → p3))) ∨ ((p5 → True) → False)) := by
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
theorem thm_5_vars_213184916572681167975239236798 : ((((p2 ∨ p5) ∨ p2) ∧ False) ∨ ((p2 ∨ p3) ∨ ((False ∨ True) ∨ ((False ∧ p2) → ((((p3 ∧ p2) ∧ False) ∧ ((p2 ∧ True) ∧ p5)) ∧ p2))))) := by
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
theorem thm_5_vars_148412983292652276289781264344 : ((((((p3 → (((False → p3) ∨ True) → (p1 → p1))) ∧ p3) → p5) → p4) → ((p1 → (p5 ∨ p3)) ∨ p4)) ∨ (p1 ∨ ((p2 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156928929966855904238387634446 : (((((((((p3 ∧ (False ∨ p1)) → False) ∧ (p5 ∧ p2)) ∨ True) ∨ True) ∧ True) ∧ (p5 ∧ p5)) ∨ p2) ∨ ((((p1 ∨ False) ∧ p5) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137093303144531222441170422771 : ((True ∧ ((p5 → ((True ∨ p3) → (((False → (False → (p3 ∧ p5))) ∧ p5) → ((p1 → p2) ∧ (p4 ∨ p1))))) ∨ True)) ∨ ((p4 ∨ p4) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344365150832436668330090415084 : (p2 → (p4 ∨ ((((p5 ∧ (p2 ∧ True)) ∧ True) ∧ ((p5 → (((p4 ∨ (p1 → True)) ∧ p1) ∨ True)) ∨ p2)) ∨ (p1 ∨ ((p5 → p2) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51491390761905721638391888968 : (((((True ∨ p3) → (p5 ∧ p1)) ∨ ((False ∧ (p3 ∨ ((True ∨ (p5 → p4)) ∧ p3))) → p3)) → (p3 → (((p4 ∨ p1) ∧ True) ∨ p3))) ∨ p4) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643242054404972367584969773813 : ((((p3 ∧ ((((p5 → p2) → (p3 → False)) ∧ p4) ∨ (p1 ∧ (((p4 ∨ ((p4 → p2) ∨ p4)) ∧ (False → (False ∧ p1))) ∧ p3)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



