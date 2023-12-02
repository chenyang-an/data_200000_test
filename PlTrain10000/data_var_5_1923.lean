variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134084738244928561445405502355 : ((((((True → p3) → (p5 → p1)) ∨ ((p3 → ((p1 ∧ p2) ∧ (p3 → False))) → ((p4 ∧ p4) → p2))) → p4) ∨ True) ∨ (p3 ∨ (p5 → False))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180403898417438861738373164561 : (((p3 ∨ (True ∨ (False ∨ (p4 ∧ (True ∨ (p4 → False)))))) ∨ (p4 ∧ p5)) → ((p5 → (p2 → (((False → p4) ∧ p1) ∨ p2))) ∨ (False → False))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h14
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
            have h16 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h11
            -- We have shown the premise of h15, we can now drive its conclusion.
            let h17 := h15 h16
            -- False on the left can always be used.
            apply False.elim h17
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115583027690647616941764032620 : ((((p3 → (p2 ∨ True)) ∨ (p5 ∧ p1)) ∧ ((p5 ∨ ((((True ∧ (p4 → True)) ∨ p3) → (p4 ∨ False)) → False)) ∧ (p5 ∧ p5))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646409553814342217844818407072 : ((((p1 → ((((((p3 ∧ True) ∧ ((p4 ∧ (p4 ∨ True)) → p2)) → False) ∧ p3) ∧ ((p3 → (False → p5)) ∧ (False ∧ p5))) ∧ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148953601485144599638885190014 : ((((p3 ∨ True) ∧ p5) ∧ (p1 ∧ (p1 → (((p4 → False) ∨ ((p5 ∧ ((p1 ∨ p3) → p4)) ∨ p5)) ∧ p2)))) ∨ ((p4 ∨ True) ∨ (p4 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159697395054030712323187036986 : ((((p4 ∨ ((True ∧ (p1 ∨ ((False ∧ p1) ∧ p2))) → ((False ∧ True) ∨ p3))) → (p4 ∨ False)) ∨ p5) → (p3 → (p4 ∨ ((p4 → False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p4 ∨ ((True ∧ (p1 ∨ ((False ∧ p1) ∧ p2))) → ((False ∧ True) ∨ p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
        apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h4
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748219926744639256903303489062 : ((((p1 → p5) → (p3 → ((((((((p2 ∨ (False ∧ p2)) ∧ False) ∧ False) → True) ∧ True) ∨ p1) ∨ p4) → ((p5 ∨ (p5 → True)) ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178008786848051954197586490090 : (((p4 ∨ ((p5 → (p5 ∧ False)) ∨ (p4 ∧ (p2 ∨ (p4 → p4))))) ∨ p2) ∨ ((True → (((p4 → (p3 → (p3 ∨ p1))) → p1) ∨ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111627876795087413876530329268 : ((((((((((((p3 ∨ (p1 ∧ p3)) ∨ True) ∧ p5) ∨ p1) ∧ p5) → p4) ∨ p3) → p5) ∧ (p4 ∨ (False ∧ p4))) ∨ p1) ∨ True) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_922858633802542436595514007726 : ((((p2 → ((True ∧ p5) → (((p3 ∧ (p1 ∧ (p5 → False))) ∧ p2) → False))) → (((p4 ∧ (False ∧ True)) ∨ ((p1 ∨ p4) ∨ p2)) ∧ p3)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((True ∧ p5) → (((p3 ∧ (p1 ∧ (p5 → False))) ∧ p2) → False))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h14 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h14
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_652166086074708000883274016179 : ((((p1 ∧ (True → (((p3 ∨ p4) → ((((False → p2) ∨ (p4 ∨ True)) → ((p1 → p2) ∧ (p4 → p2))) ∨ p4)) ∧ p2))) ∧ (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113488972650396259818933846965 : (((((True → False) ∧ (((p3 → (p5 ∧ True)) ∧ (p5 ∨ ((p1 ∧ (p1 ∧ True)) ∧ p3))) ∧ True)) → (p2 ∧ True)) ∨ (p3 ∨ p5)) ∨ (p1 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h18 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h19 := h2 h18
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350354898561500576182252391697 : (p4 → ((p5 → ((((p1 ∨ ((p1 ∨ (False ∧ p3)) → p1)) → (p5 ∧ p3)) ∨ (p4 ∨ (((p5 → False) ∨ (p3 ∨ p2)) → p1))) ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307503907148063046515378937898 : (p1 ∨ (True → ((((p5 ∧ False) ∧ (((p4 ∨ p2) → p2) ∧ p4)) ∧ ((p4 → (p5 ∧ True)) ∨ p2)) ∨ (((True → False) → (p5 ∨ p1)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330742505735893501365995485921 : (True → (p1 → ((((p1 ∧ True) ∨ (True ∧ ((p5 → False) ∨ True))) ∨ (p1 ∨ (True ∧ p1))) → ((p5 ∧ ((p3 ∧ p3) ∨ (True → p3))) ∨ True)))) := by
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
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119405205837778884825094662880 : ((p4 → (((p1 → False) ∧ (((p5 → (p3 ∨ (p5 ∨ ((True ∧ True) ∧ (p2 ∨ p4))))) → ((False ∧ True) ∨ p4)) → p1)) ∨ p3)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711983095423109491625381995082 : ((((((p3 ∨ (p5 → p1)) ∨ p3) ∨ p3) ∨ ((p2 ∨ (True ∧ ((p1 → False) → ((p4 ∨ True) → ((p2 ∨ (True → False)) ∨ False))))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231743605796130592703038127840 : (((p3 ∧ True) → p2) → ((((p3 ∨ False) ∨ (p2 ∧ (p3 ∨ (p3 ∧ (p2 ∨ ((True ∨ p5) ∧ p3)))))) ∨ (p2 → True)) ∨ ((p4 ∨ p4) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159089056903494785711603447869 : ((True → (((((p2 → p4) ∨ (p4 ∧ True)) → (p3 → (p1 ∧ (p1 ∨ p4)))) ∨ True) ∨ (False ∧ p3))) ∨ (True → ((p3 ∧ p2) → (p5 ∧ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597706186547677563386499909678 : (((((True ∧ ((True ∨ True) ∧ True)) → (p1 ∨ (((((False ∨ ((p4 ∧ False) ∧ p5)) → p4) ∧ p2) → (p3 → (False → False))) ∧ p3))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122358926805171488100425110774 : ((((((((False ∧ p5) → p5) ∨ ((p2 ∧ (p2 ∨ p5)) ∧ (p5 ∨ (True ∧ p1)))) ∨ (p4 → p2)) ∨ p2) ∨ p3) ∨ (p2 → p4)) → (p1 ∨ True)) := by
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
            -- Conjunctions on the left can always be decomposed.
            let h8 := h7.left
            let h9 := h7.right
            -- Conjunctions on the left can always be decomposed.
            let h10 := h8.left
            let h11 := h8.right
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Disjunctions on the left can always be decomposed.
              cases h9
              case inl h13 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h14 =>
                -- Conjunctions on the left can always be decomposed.
                let h15 := h14.left
                let h16 := h14.right
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h16
            case inr h17 =>
              -- Disjunctions on the left can always be decomposed.
              cases h9
              case inl h18 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h19 =>
                -- Conjunctions on the left can always be decomposed.
                let h20 := h19.left
                let h21 := h19.right
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h21
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h23 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726354281305580138685362707063 : (((((p4 ∨ p4) ∨ p4) ∨ ((p5 ∨ True) ∧ (((p5 ∧ (((p1 ∧ (True → p2)) ∨ p2) ∧ (p2 → (p3 ∨ False)))) ∨ False) ∧ (p3 → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172781392236428097875926036980 : (((p5 ∨ p1) → ((((((True ∧ p1) ∨ p5) ∧ p2) ∧ p4) ∨ (p4 ∨ True)) ∨ False)) ∨ (((True ∨ p1) ∧ ((True ∨ True) ∨ (p1 → True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98793389042520070907016723145 : ((True → ((((((p3 ∨ p5) ∨ True) → ((p1 ∧ (p3 → (((False → p3) ∨ p2) ∧ p2))) ∨ (p5 ∨ (p4 ∧ p4)))) ∨ p2) ∧ p3) ∧ p2)) → p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112904294815575314663532205717 : ((((p2 ∧ p2) ∨ (p5 → ((((p5 → p3) ∧ p1) → ((p5 → (p1 → False)) ∧ ((False → p5) ∧ (p5 → p5)))) ∨ p5))) → False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164797523289145606224178086420 : (((((p3 ∨ p3) → p5) ∧ (((p1 ∨ p5) ∧ ((p2 ∨ (False ∧ p3)) ∨ p5)) → p1)) ∨ True) ∨ ((False ∧ (False → (p1 ∧ (p3 → p1)))) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37465789862355688615295532284 : (((((((True → p2) → p3) ∨ ((p4 → p3) → p3)) ∨ ((p1 → ((p4 → ((p4 ∨ (p4 ∨ True)) ∨ p3)) ∧ p4)) ∨ p1)) ∨ True) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633683117716688420829209553960 : (((((p2 ∧ ((((True ∨ True) ∧ ((True → ((p1 ∨ p3) → True)) → False)) ∨ ((p1 ∧ p4) → p2)) ∧ (False ∨ p4))) ∨ (p3 → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138139180553518204198651862871 : ((p1 → (((((p5 ∧ (p1 ∨ (p3 → False))) → (False ∧ (p4 → False))) ∨ (((p4 → p4) ∧ p5) ∨ p1)) ∧ p3) ∧ p2)) ∨ ((p3 ∧ p2) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117755846615412498794866816559 : ((p4 ∧ (((((False → (True ∨ p1)) → ((((p4 ∧ p4) ∧ ((p3 → (p4 ∨ True)) → p3)) ∨ p5) ∧ p5)) ∧ p4) ∧ p3) → p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743479384916299201154572168336 : ((((p5 → p4) ∨ (((p2 ∧ ((p3 → True) ∧ p5)) ∧ (p4 ∧ p2)) → (((p4 → False) ∨ ((p1 → p1) ∧ (p2 ∨ (p5 ∧ True)))) ∨ p3))) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h3.left
  let h9 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206560803849501062906559483104 : ((True → (p4 ∨ ((True → True) → False))) ∨ ((p2 ∧ (p4 ∧ (((p2 ∨ ((p5 ∧ p4) ∧ False)) ∧ (False → p2)) ∨ False))) → (p1 ∨ (p3 ∨ p4)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234262887632178887772267432324 : ((False → (True → p2)) → ((False ∨ (((p5 → True) → (p4 ∨ p4)) ∧ True)) → (p5 → (((p2 ∨ p2) ∧ p1) ∨ (p5 ∧ (p5 ∨ (True ∧ p1))))))) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114399119688564359739518036686 : ((((p1 ∨ ((True ∧ True) → (((p3 ∧ True) ∧ True) → p3))) → ((False ∧ (True ∨ p3)) ∨ p3)) ∨ (False ∨ (True ∧ (p5 ∧ False)))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328145226248946506031841416603 : (True → ((False ∨ (p1 ∧ (p5 ∧ (((p1 → ((True ∨ False) ∨ True)) ∧ ((p4 ∧ p2) ∧ (True ∨ False))) ∧ (True ∨ p2))))) ∨ (True ∨ (False ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341880991174743358663161572022 : (p2 → ((p5 ∨ ((((((True ∧ p4) ∨ (True → False)) → ((p5 ∧ p2) ∧ p3)) ∨ (p2 ∧ p4)) ∨ p2) ∧ ((p2 ∧ p1) → p4))) → (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149241762563531228674566645210 : (((False ∨ p1) ∨ ((((False ∧ p3) ∧ p5) ∧ p3) ∧ ((((p4 ∨ p3) ∧ p3) ∨ p2) ∧ (p2 → (p5 → p4))))) ∨ ((True ∨ True) → (p5 → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200346826100682097223272428718 : (((p4 ∨ p5) ∧ (True ∨ (p1 ∧ (p3 ∨ True)))) → (((p5 → (True ∧ True)) ∨ (True → p4)) ∧ ((p1 → ((p2 ∧ (True → True)) ∧ False)) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h23
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h24 := h1.left
  let h25 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h24
  case inl h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h32 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h34 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h39 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201010565875168339655521644995 : ((p3 ∨ (p1 ∨ (((p3 ∨ p2) → p1) → p2))) → (p5 → (((p2 ∧ p4) ∧ ((False ∧ p3) → p3)) → (((p1 ∧ p1) ∧ (p5 ∧ p3)) ∨ p2)))) := by
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
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_988437022026305402521656984053 : (((p3 ∧ (((((p3 → p5) ∧ ((p1 → ((False ∨ p2) → False)) ∧ p4)) ∧ p2) ∨ (((p4 → p3) → p1) ∨ (p3 ∨ (False ∨ False)))) → False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((p3 → p5) ∧ ((p1 → ((False ∨ p2) → False)) ∧ p4)) ∧ p2) ∨ (((p4 → p3) → p1) ∨ (p3 ∨ (False ∨ False)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301422959368785376725669066393 : (False ∨ (((p5 → (True ∨ True)) → p1) → ((((p4 → (p4 → False)) → p2) ∨ p3) ∨ ((p5 ∧ False) → ((p1 → (p2 ∧ (p3 ∧ p5))) ∨ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768769050133808266376820831565 : (((p5 ∧ ((False ∨ (False ∨ ((p5 ∨ p3) ∨ (p3 → False)))) ∨ (((p3 ∨ (((p5 ∨ (p2 ∧ (False ∨ p5))) ∧ p5) ∨ p2)) → p4) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138742096680427783785435683783 : ((((False → (True → (True → True))) → (p2 ∧ ((((p3 → (((p5 ∨ p2) ∧ p3) ∨ p1)) ∧ p4) ∨ True) ∧ False))) ∧ p2) → ((p3 ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → (True → (True → True))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708018575997734043511931346850 : ((((p2 ∨ ((p2 ∧ (p2 → (False ∨ p3))) ∨ p4)) ∨ ((False ∨ (p2 ∧ p4)) ∧ (p2 ∨ (p3 ∨ (False → (p5 → (p2 → (p1 ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46103838206813276363898056192 : (((((p1 ∧ p1) → (((True ∨ (p3 ∨ p5)) ∧ True) → (p5 ∧ (False → (((p3 → (p3 ∧ p1)) ∨ p2) ∨ p3))))) ∨ p1) ∧ (p3 ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67689875799861488089938068460 : ((p1 → (p2 → (p4 → (p4 → (p5 ∨ (((p4 → p4) ∧ ((p3 → ((True ∨ p1) → p5)) → (p5 ∧ True))) ∨ (p3 ∧ (p5 ∧ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247575608328643513446120888201 : ((False ∨ p4) ∨ (p4 ∨ (((False → p4) → p4) ∨ (p1 ∨ (False → ((p1 ∨ (((p1 → p5) ∨ (p2 ∨ ((p3 ∨ p1) ∧ p5))) ∧ p5)) ∧ p3)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152128191022295332210936061419 : ((((True ∨ False) → (p4 ∧ ((p3 ∨ p2) ∨ p4))) ∧ (False → (p4 → ((p3 → ((p3 ∧ p1) ∨ p3)) ∧ True)))) → ((p4 ∨ (p4 ∧ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66186053947325843551555189056 : ((p5 ∨ (((((p1 ∨ True) ∧ ((p2 → (((True → (True ∧ p2)) ∨ p4) ∨ p1)) ∧ True)) ∨ p2) → p5) → (((p5 ∨ p4) ∨ p3) ∨ False))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ True) ∧ ((p2 → (((True → (True ∧ p2)) ∨ p4) ∨ p1)) ∧ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8057390829101938438185136884 : ((((((((p2 ∧ p1) ∨ (p4 → p5)) ∧ (p4 ∨ p5)) → (True ∧ (p4 ∧ True))) ∧ (p5 → (p4 ∧ (True → (p1 ∧ False))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48466071228268099282723503013 : (((((((True ∨ (p3 → p2)) → p4) ∧ (p2 ∨ ((p1 ∧ (p2 → (True → p2))) ∧ p5))) ∧ (False → True)) ∧ p1) ∧ ((True ∨ p5) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3295619450404526303084967281 : ((True ∧ p4) → ((((p3 ∨ p1) ∧ False) ∨ ((False ∧ True) ∧ p2)) ∨ ((p1 → p4) ∨ (p3 ∨ ((p2 ∨ (p4 ∧ p5)) ∧ (p1 ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258764969309218102562908806344 : ((True → False) → (((p1 → (((p2 → p4) ∨ (True → ((p2 ∨ True) ∨ p3))) ∧ p4)) → ((((p5 ∧ False) ∨ (p4 ∧ p4)) → p5) ∧ True)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174204012404686766609336210923 : ((((((p2 ∧ False) → ((p1 ∨ p2) ∨ (p3 ∧ p2))) ∧ p3) → p4) → (p1 → p1)) → ((p3 ∨ ((p3 ∧ (False ∨ p4)) ∨ (False → p4))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248742571108945088635078625231 : ((p3 ∨ p3) ∨ ((((((((False ∨ ((p5 ∨ False) ∧ False)) ∨ p1) ∧ False) → p5) ∨ (p3 ∧ p2)) ∧ (p5 ∧ (p1 ∨ (True ∧ p2)))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624697809894381525637269009390 : ((((p4 ∨ (p1 ∨ ((p5 ∨ (True → (((p5 ∨ p4) ∨ False) ∨ ((False ∧ (p4 ∧ (p2 → (p2 ∨ True)))) → (p5 → p2))))) ∨ p4))) ∨ p1) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61384459677925546132825883259 : ((p1 ∧ ((((p3 ∨ (((False → p1) → p5) ∧ (p1 → ((p2 → (p1 → (p1 → p3))) ∨ p3)))) → p5) ∨ ((p3 ∧ p1) ∨ False)) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171564589497126024684239835726 : ((((p3 → ((p4 ∧ p1) ∨ (p5 → (p3 → ((p2 ∧ p2) ∨ True))))) → p2) ∨ p1) ∨ ((p3 → True) ∧ ((False ∨ False) → (p1 → (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264444007526119839451598250989 : (True ∧ (((True → p5) ∨ (p1 ∨ True)) → (p1 → (((((False → p5) ∨ (((False ∨ p5) ∨ p4) ∧ (p5 → (False ∧ False)))) ∨ p2) → p2) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_17896829894522126617220202737 : ((((p3 ∨ ((p2 → True) → (((True ∨ (((p5 ∧ p3) ∧ p3) ∧ p1)) → p2) ∧ (p5 ∨ False)))) → p4) ∨ (((p2 ∨ True) ∨ p5) ∨ p2)) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151788316834609718523018360668 : (((p2 ∨ ((p2 ∧ (p4 ∧ ((True ∧ (p1 ∨ p4)) ∧ p4))) ∨ (p1 → (p3 → p2)))) → (True ∧ (p4 ∧ True))) → (((False → p2) → False) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → p2) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135513330525344974948526394011 : (((p4 → ((((p2 ∨ p5) ∨ ((p2 → ((False → p5) → (True ∧ False))) → p5)) → True) ∧ p5)) → ((False ∨ p2) ∧ True)) ∨ ((p1 → True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204267198596250244626776595353 : ((((p4 ∨ p2) ∨ (p1 → True)) ∧ p2) ∨ ((True → ((p5 ∧ p2) ∨ False)) ∨ (p2 → ((p1 ∧ p2) → (False ∨ (((p4 ∨ p2) ∨ False) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116337418119393822280789693906 : ((((p3 → p2) ∧ p5) → ((p2 ∨ ((p2 → p1) ∧ ((p4 ∧ p4) ∨ ((False ∨ (((p2 ∨ p2) → p2) ∧ p3)) ∨ p1)))) ∨ True)) ∨ (p2 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_247379129608586403200425084838 : ((False ∨ p1) ∨ ((True ∨ p3) ∧ ((p2 ∨ ((p1 → ((False ∧ ((p2 ∨ p3) ∨ p3)) ∧ (p5 ∨ True))) ∧ (p5 ∧ ((False → p2) ∨ False)))) ∨ True))) := by
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
theorem thm_5_vars_43336036534892857518932964515 : ((((((p2 ∨ ((False → p2) ∧ ((p4 → False) → (False ∧ (p4 → p2))))) ∧ ((p2 → ((p4 ∧ p1) → p5)) → p2)) → True) ∨ p5) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261514654520226690604361857280 : ((p5 → p3) → (((p3 ∨ ((p1 ∨ (p3 ∨ (p2 ∨ p3))) ∧ p4)) → (((False ∨ p1) → False) ∨ (p2 ∨ True))) ∨ (((p5 → p2) ∨ False) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312379400498815597478734565786 : (p2 ∨ (p3 → ((p3 → (False → (True ∧ p5))) → (((p2 → (p5 ∧ (p1 ∧ False))) → (True → p2)) → ((((p1 ∨ p3) ∧ p1) ∧ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221527461441930035799540974855 : (((p2 → p2) ∨ p3) ∧ ((p5 ∧ p5) → ((False ∧ ((p4 → False) ∨ ((p5 ∧ ((p5 ∨ (p1 ∧ p2)) → ((p2 ∧ False) ∧ True))) ∧ True))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
theorem thm_5_vars_119851862784638142450172293384 : ((((p3 → (((((False → ((False → (p5 ∧ (False → p5))) ∧ p5)) ∨ True) ∧ p1) → True) → (p1 ∧ (p1 ∨ p5)))) → True) ∧ p3) → (p5 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49149973376897521242720423066 : (((((p1 ∨ False) → (((True ∨ True) → p4) → p3)) ∧ ((True → p1) ∧ (p3 ∧ ((p4 → (False ∨ False)) ∨ p3)))) ∨ ((p1 ∨ p3) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303138685570451744312460017073 : (False ∨ (p3 → ((True → p4) ∨ ((True → ((p2 → p4) → p2)) ∨ (p1 ∨ (((p5 ∨ p5) ∧ (False ∧ (p4 ∨ ((p2 ∨ p4) ∧ p1)))) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_607562544310394021100190654754 : (((((p1 ∧ ((p4 → ((((p5 ∧ ((p2 ∨ p1) → (p3 ∧ (p2 ∧ p2)))) → ((p3 ∧ True) ∧ p5)) → p2) → p2)) → p3)) ∧ p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137685073283705669289203967849 : ((p1 ∨ (((p3 → ((((p2 → p2) → p4) → p2) ∨ (p4 ∨ (p2 → False)))) → (p2 ∨ ((True → p5) → False))) ∨ p2)) ∨ ((p1 ∧ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314096572893021073017525126791 : (p3 ∨ (((((p5 → p4) ∧ (p5 → p3)) ∨ (p4 → (p3 ∨ p4))) → ((p5 ∧ p5) ∧ (p2 ∧ (((False ∧ p2) ∧ p5) ∧ False)))) → (p1 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → p4) ∧ (p5 → p3)) ∨ (p4 → (p3 ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (((p5 → p4) ∧ (p5 → p3)) ∨ (p4 → (p3 ∨ p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h8
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112660938690408300399146531936 : (((((((((p1 ∨ (False → p3)) ∧ p3) ∨ p3) → (p3 ∧ (False ∨ (p5 ∧ p5)))) ∨ p3) → True) ∨ (p2 ∨ (p2 ∧ True))) → p5) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773593274826544079884002274094 : (((False ∨ (((p4 ∨ p5) ∨ (((p4 ∨ p3) ∨ (((p5 ∧ False) ∨ (p4 ∧ p3)) ∨ ((p3 ∨ ((p1 → False) ∨ p2)) → True))) ∧ True)) ∨ p5)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350195863088467262443879216698 : (p4 → (((p4 → (p2 ∧ p3)) ∧ (p4 → (p2 ∨ ((((True ∨ (p5 ∧ (p2 ∧ p3))) → ((p1 → (p2 → p1)) ∨ p1)) ∨ p4) → p5)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620972997377274252174922117639 : (((((p5 ∨ p4) → (((((p2 → (((p4 → p3) ∧ p5) ∧ p3)) ∨ (((p4 ∧ True) → p1) ∧ True)) → p2) ∨ p1) ∧ (p1 ∨ p2))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49754814994370780425456274213 : (((True ∨ (((p5 → (p5 ∨ False)) ∨ ((p1 ∨ (((True → p1) ∧ p2) → True)) ∨ ((True → True) → p5))) ∧ p4)) → (p5 ∨ (True ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714957551068257659371213739784 : ((((True ∨ ((p1 ∨ False) → (p4 → True))) → ((p4 → (((p1 ∧ p3) ∧ (False → (False ∨ (False ∨ (True ∨ p1))))) ∨ p3)) ∨ (p5 ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616291317867826886030565651363 : (((((((((p5 → False) → (p2 → p5)) → p2) ∧ True) → (p3 ∧ p3)) ∨ ((True → ((p1 ∨ (True ∨ True)) ∧ p5)) ∨ (p1 ∨ True))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66289676953309740116473463155 : ((p5 ∨ ((p2 → p4) ∧ ((((p3 ∨ (False → (p1 ∨ ((p5 ∨ (False ∨ p3)) ∧ False)))) → p2) ∧ p5) ∨ ((p3 → p4) → (p2 ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62239408911407036529357172329 : ((p3 ∧ (((((p2 ∧ (p2 ∨ (p5 ∧ p3))) ∨ False) ∧ (p3 ∧ p5)) ∨ (False → (p3 ∧ ((((p2 ∨ p4) ∧ False) ∧ p5) → p1)))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789969762275884604640522250850 : (((p5 ∨ ((p3 ∨ p5) ∧ ((True ∧ ((p2 ∨ False) ∧ (p2 → p4))) ∧ (((((p5 ∨ p3) → (p4 ∨ True)) → (p4 → p4)) ∨ True) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134177746340420753234608337530 : ((((p1 ∨ ((p3 ∧ p1) → ((p2 → ((p3 ∧ (False ∧ True)) ∧ p4)) ∨ p2))) → (p5 ∧ (p3 ∧ (p3 ∧ False)))) ∨ p1) ∨ (p1 ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355553052337327805176057319097 : (p5 → ((((((p2 ∧ (True ∧ ((True ∨ (p3 ∧ True)) ∧ True))) ∧ p1) → False) ∨ ((True ∨ (p2 ∧ (p3 → True))) ∧ p1)) → False) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191784559223482187611798456713 : ((p1 ∨ (False ∨ (p4 ∧ (((True → p1) ∨ p4) → p1)))) ∨ (p1 ∨ ((False ∧ (((p2 ∨ p1) ∨ False) → (p5 ∨ (True → p3)))) → (p4 ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199811625957566402409243385231 : (((((True ∧ p4) ∨ True) → p4) ∧ (p4 ∧ p2)) → (p1 → (p2 → ((p4 → ((False ∨ (p5 ∧ (((p3 → False) → p3) → p3))) ∧ p3)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179434086897214748553546816392 : ((p4 ∨ (p3 ∨ (((((p5 ∨ (p3 ∧ p2)) → True) ∧ p3) → p4) ∨ p1))) ∨ ((p1 → (((False → (p1 ∧ p5)) ∧ p1) ∧ (True ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183976226094148343548235907182 : (((p5 → ((p3 ∨ (p2 ∧ False)) ∧ (p1 ∨ (p2 → p1)))) ∧ False) ∨ (((((False → False) ∨ (p2 → (True ∨ p2))) ∨ (p3 ∨ p4)) → True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213341996350646509942199296661 : (((p2 ∧ (p3 → p4)) ∧ p1) ∨ ((True → ((p4 → ((p4 → ((True → p2) ∨ (p4 ∧ True))) ∧ (p5 ∨ (True ∧ p4)))) → p2)) → (p1 → p2))) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → ((p4 → ((True → p2) ∨ (p4 ∧ True))) ∧ (p5 ∨ (True ∧ p4)))) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h6
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712761162327041213244566229620 : (((((p2 ∨ p4) ∨ (p3 → (p2 ∧ p2))) ∨ (p2 ∧ ((((p2 ∨ ((((p2 → p5) ∨ p3) → p4) → (False ∧ p5))) ∧ False) ∧ p3) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118244197849716237442639238064 : ((p1 ∨ ((((p2 ∧ False) → p4) → ((p1 ∨ p2) ∨ (((p2 ∧ True) → p4) ∧ ((p3 ∧ (p2 ∧ p5)) → p1)))) ∨ (p5 → True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95073284581913987780583674266 : ((p4 ∧ (((False ∨ True) → ((p4 ∧ p5) ∨ ((p3 ∨ p2) ∨ (((False ∨ ((p4 ∧ False) → (p3 ∧ p3))) ∧ True) ∧ (p2 → True))))) → False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ True) → ((p4 ∧ p5) ∨ ((p3 ∨ p2) ∨ (((False ∨ ((p4 ∧ False) → (p3 ∧ p3))) ∧ True) ∧ (p2 → True))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- False on the left can always be used.
      apply False.elim h12
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h4
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300415281620658683270887208886 : (False ∨ ((p3 → (((p4 → ((p1 ∨ False) ∧ (((p5 ∨ False) ∧ (p5 ∧ p5)) → ((p4 ∨ True) ∧ True)))) → p4) ∨ p3)) ∨ (p3 → (False ∨ p2)))) := by
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
theorem thm_5_vars_258796430692364328927077591971 : ((True → False) → ((p1 ∨ False) ∧ (((p5 ∧ ((False ∨ False) ∧ (((p1 ∨ p1) ∧ p3) ∧ p5))) → (p3 ∧ p5)) ∧ (((p5 ∨ p2) ∨ p1) ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h4.left
  let h12 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h17 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h17
  -- False on the left can always be used.
  apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66293884419263439235793742309 : ((p5 ∨ ((p3 ∧ p4) ∨ ((((p1 ∨ p4) ∧ p2) ∨ (p2 → True)) ∨ (p5 ∧ (False → (p3 ∧ ((p5 ∨ False) ∧ ((True ∧ False) ∨ False)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248288387131008260761799381468 : ((p2 ∨ p2) ∨ ((p2 ∨ (p3 ∧ p4)) ∨ (((p2 → (((p5 → ((p3 → (p3 ∧ p3)) ∧ p4)) ∧ (p1 ∨ False)) ∧ (p4 ∧ p5))) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134275593342888381343594820442 : ((((p5 ∨ p2) ∧ (p4 ∧ (((p4 ∧ (((True ∧ True) → p5) → ((p2 → False) → (p5 ∧ False)))) ∨ True) ∧ p5))) ∨ p3) ∨ (True ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



