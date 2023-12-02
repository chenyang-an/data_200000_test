variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113441517991800973851123189468 : (((((p3 ∧ ((p1 → False) ∨ p4)) → ((p1 ∧ p4) ∨ ((True ∧ p5) ∧ ((p4 ∧ (p5 ∨ p1)) ∧ p2)))) ∨ p4) ∨ (True ∨ p2)) ∨ (False ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165565197161549039335533281881 : ((((p4 ∧ ((p2 → (False → p2)) ∧ p2)) ∧ p5) ∨ ((True ∨ (p1 → (p4 ∧ p3))) → p4)) ∨ (p4 ∨ (p1 → (True → (False → (p1 ∧ False)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156693347138145170653250481724 : ((((p3 ∨ (p3 → ((False ∨ ((p1 → p4) → p5)) ∨ (True ∧ p1)))) ∧ (p2 → (False ∨ p3))) ∧ p2) ∨ (p2 ∨ ((p3 ∧ (True ∧ p1)) → p3))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207038018169892673163610118164 : ((((True → p1) → (p1 ∧ p4)) ∧ p3) → (((p3 → p1) → (((p2 ∨ p1) → ((True → True) → False)) → p5)) ∧ (((p2 ∨ True) ∨ p3) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : (p2 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h6
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (True → True) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h10
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the left can always be decomposed.
  let h13 := h1.left
  let h14 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114839770808686606908236900986 : (((((False ∨ (((p5 ∨ p3) ∧ p4) ∨ p5)) ∨ (True ∨ (p4 ∧ p3))) ∧ p5) ∨ (p2 → ((p1 ∧ p1) ∧ (p5 ∨ (False → p2))))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43946502931892126348053214655 : (((((p1 ∨ (p4 → (p3 ∨ p4))) → (p4 ∧ ((p4 ∧ ((p5 ∧ (p4 ∨ (p5 → p5))) ∨ False)) ∧ (p5 ∨ p1)))) ∨ (p2 ∧ p5)) → p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (p1 ∨ (p4 → (p3 ∨ p4))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54317178613304160435201840583 : (((True ∧ ((False ∨ p3) ∧ (p5 ∨ (p4 ∨ p5)))) ∧ (p1 → (((False ∧ ((p2 ∨ p3) → ((p2 ∨ (p4 ∨ p5)) ∧ p2))) → p2) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113732271841084271990881843899 : (((((p2 → p5) ∨ (((((p3 ∨ p3) → p2) → p1) ∨ (p4 ∧ p3)) ∨ (p1 ∧ p3))) → (True ∨ (p5 ∨ True))) → (False ∨ p5)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219006663863135969583642672549 : ((p4 ∧ (p5 ∨ (False ∧ p2))) → ((True ∨ ((True ∧ (True ∨ (p2 ∨ p3))) ∨ p4)) → ((p2 → (p1 ∨ (p2 ∧ True))) → ((False ∨ p4) ∨ False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h19.left
          let h21 := h19.right
          -- False on the left can always be used.
          apply False.elim h20
      case inr h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h1.left
          let h25 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h27 =>
            -- Conjunctions on the left can always be decomposed.
            let h28 := h27.left
            let h29 := h27.right
            -- False on the left can always be used.
            apply False.elim h28
        case inr h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h1.left
          let h32 := h1.right
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- False on the left can always be used.
            apply False.elim h35
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h1.left
      let h39 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h38
      case inr h41 =>
        -- Conjunctions on the left can always be decomposed.
        let h42 := h41.left
        let h43 := h41.right
        -- False on the left can always be used.
        apply False.elim h42



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167037002158768063874309938460 : (((((False ∨ p3) ∨ ((True ∨ ((p1 ∨ (p2 ∨ (p3 ∨ p1))) ∨ True)) ∨ p5)) ∧ p3) ∨ False) → (((p5 → p1) ∨ True) ∧ (p4 ∨ (p1 → True)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
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
                -- Disjunctions on the left can always be decomposed.
                cases h16
                case inl h17 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h18 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h32
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h33 =>
          -- Disjunctions on the left can always be decomposed.
          cases h33
          case inl h34 =>
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h35 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h36
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h37 =>
              -- Disjunctions on the left can always be decomposed.
              cases h37
              case inl h38 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- Implications on the right can always be decomposed.
                intro h39
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h40 =>
                -- Disjunctions on the left can always be decomposed.
                cases h40
                case inl h41 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Implications on the right can always be decomposed.
                  intro h42
                  -- True on the right can always be proven directly.
                  apply True.intro
                case inr h43 =>
                  -- Show the right disjunct based on <expert-advice>.
                  apply Or.inr
                  -- Implications on the right can always be decomposed.
                  intro h44
                  -- True on the right can always be proven directly.
                  apply True.intro
          case inr h45 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h46
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h48
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h49 =>
    -- False on the left can always be used.
    apply False.elim h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115089852484553106774196175796 : (((p5 ∨ (p1 ∨ (p4 ∨ (True ∧ (p4 ∧ (p5 ∨ (p2 ∧ False))))))) ∨ (p2 ∧ (p1 → (p1 ∧ (p3 → ((p1 ∧ p3) ∨ False)))))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69325126014305953239852438013 : ((p5 → (p5 ∧ (((p4 ∨ ((p5 ∨ ((False ∨ (p1 → False)) ∧ ((True → p1) ∨ p2))) ∧ False)) → (p4 ∨ True)) → ((p5 ∨ p2) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135739342901298930002306033218 : ((((p3 ∧ ((p2 ∨ (p4 ∧ (p3 → True))) → (p3 ∧ True))) → (True ∧ p1)) ∨ (True ∧ (p3 → ((p3 → True) → p2)))) ∨ (False → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207462807553608943173882237687 : (((True → (p2 ∧ (p1 ∧ p5))) ∨ p3) → ((p3 → False) → ((((((p5 ∨ p4) ∧ p1) ∧ (False ∧ ((p4 → p3) → True))) ∧ p1) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259815840015948076503541941300 : ((p1 → p3) → (((True → (((p4 → (p4 ∨ (True → p3))) ∨ p2) ∨ (p5 ∧ (p4 → p2)))) → p4) ∨ ((p4 → True) ∨ ((p1 ∨ p4) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66072339116131991092568913246 : ((p5 ∨ (((p5 ∧ p2) ∨ (p2 ∧ (((p5 ∨ (((p2 ∨ True) ∧ p2) ∨ p3)) → (p1 → (p2 ∧ (p4 ∨ (p5 ∨ p1))))) ∧ p3))) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136373215369006088568065083537 : (((((True ∨ p1) → p5) → p1) ∨ ((p2 → ((p4 → (False ∧ ((p5 ∨ (p2 ∨ p5)) → p3))) ∨ (p2 → p4))) → p1)) ∨ (True ∨ (p2 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647278241258684970166102781155 : ((((p4 → (((p3 ∨ ((((True ∧ (p3 ∨ ((((p2 → p2) → p1) ∧ (p3 ∧ False)) ∧ p5))) ∨ p4) ∨ p3) ∧ p1)) ∧ p3) → p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301106361519516154620246836223 : (False ∨ (((((p3 ∨ p5) ∨ True) ∧ (p2 ∧ p2)) ∨ True) ∧ ((((((p1 ∧ p5) ∧ p5) ∨ ((False → (False ∨ True)) ∧ True)) ∨ True) → p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609551439003127476639615350246 : (((((p3 ∧ ((p2 → (p1 → p4)) ∨ (((p5 → p2) ∧ (p3 ∨ p3)) → ((((p5 ∨ (True → False)) ∨ True) ∨ p2) ∧ p2)))) ∨ p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88100839698547107174036378074 : ((((True ∧ (p1 ∧ p2)) → p1) ∧ ((((p5 ∧ ((p5 → p3) ∨ ((True ∨ p1) → p2))) ∧ (p4 → p4)) ∧ p3) ∧ ((p2 ∨ p4) → p2))) → p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171966401999463561352438207757 : (((True ∧ ((p4 → ((p5 ∨ p1) ∧ p2)) ∧ (p5 ∨ (False ∨ p4)))) ∧ (p1 → p2)) ∨ ((False ∨ (((p1 ∨ (False ∨ True)) ∧ p3) ∧ False)) → p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257098184179090164280127845459 : ((p2 ∨ False) → ((p2 → p1) ∨ ((((p1 → p1) → ((p2 → ((p1 → p3) ∧ (p1 → False))) ∧ p5)) ∧ (False ∧ p4)) ∨ ((p2 → True) ∨ False)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313053923764151991408922914378 : (p3 ∨ ((((False ∧ (False ∧ True)) → (((p1 ∧ ((p4 ∧ (((p3 ∧ p3) ∨ (p4 ∧ p5)) ∨ (False ∧ False))) ∧ p5)) → p3) ∨ True)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710925187932491799490921481028 : (((((p1 ∨ p4) ∨ ((p3 → p3) ∨ p1)) ∧ (((p2 ∧ True) ∨ p4) ∨ (False ∧ ((True ∨ p2) ∨ ((p4 ∨ ((False → p1) ∨ False)) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330382314411248379003641610932 : (True → (p2 ∨ ((p4 → ((True → (p2 → p2)) → (p2 ∧ True))) → (((((((True ∧ p5) ∧ (True ∧ p5)) → p2) → p1) → p3) ∨ True) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112646199917062436570497155143 : ((((((((True ∨ True) → (True ∨ True)) → ((((p3 → p5) ∨ p2) ∧ p1) ∧ p3)) → p3) ∧ True) ∧ (p4 → (False ∧ p4))) → False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62000888596975764196759473895 : ((p2 ∧ ((p3 ∨ (p4 ∧ (p5 ∧ p5))) ∧ (p5 ∨ (p3 ∧ (((p2 ∧ True) ∨ ((p3 ∧ p1) ∨ (p4 → p3))) → ((p1 → p5) → p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646924868042684556634059332211 : ((((p2 → (True → (((p4 ∧ (p3 ∧ ((((((p5 ∨ p3) → p1) ∧ p2) ∨ True) → False) → p1))) ∨ p1) ∨ ((p5 ∨ p2) ∧ p4)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148667615641247832838939362415 : (((((((p1 ∧ p1) ∧ p4) ∨ p4) ∧ p3) ∧ p1) ∨ (p2 → (p3 → (p5 ∧ (p5 → ((p2 ∧ p4) ∧ p2)))))) ∨ (True → ((p2 ∧ p2) → p2))) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312288318876237398141276342135 : (p2 ∨ (p2 → (((p4 ∨ ((p4 ∧ p2) → ((p4 ∧ ((p3 → ((p2 ∧ p1) ∧ (False → (True → (p4 ∧ p2))))) → p3)) ∧ p3))) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246487101155515143183157245499 : ((p5 ∧ False) ∨ (p3 → (((((False ∨ (p4 ∧ p1)) ∨ (p3 ∨ (p4 → p5))) → (True ∧ (False ∧ (True → True)))) → p5) ∨ ((p2 ∨ p3) ∨ p3)))) := by
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
theorem thm_5_vars_62223857818397867184957231721 : ((p3 ∧ ((((((p1 → p3) → ((p3 → False) ∨ ((((False ∧ p1) ∨ p5) ∨ True) → ((p4 ∧ True) → p2)))) ∨ p3) ∨ p4) ∨ True) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149673921218347099511734212744 : ((p5 ∧ (((p3 ∧ (((True ∧ p2) → (p3 ∨ p4)) ∨ True)) ∨ (p5 ∨ ((p4 ∧ p3) ∨ (p3 ∧ p1)))) ∧ p5)) ∨ (False → ((p4 ∨ p4) ∧ p5))) := by
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
theorem thm_5_vars_56295780502637657672415824904 : (((((p3 ∨ p3) ∨ p5) ∧ p2) → ((((p5 ∧ True) ∨ ((False ∨ False) ∧ True)) ∨ (p3 ∧ (p4 ∨ (p1 ∨ p4)))) ∨ ((p2 ∨ p1) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606286611451619479591338362633 : ((((((p2 → ((((((p4 → True) → (p2 → (p1 → True))) → p4) ∨ False) ∧ True) → (((p1 ∧ False) ∨ p3) ∧ False))) ∧ p4) ∧ p3) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_135547353994101088341200134222 : ((((False ∧ (p4 → False)) ∨ (p2 → ((((p5 ∨ (p1 ∧ p1)) ∧ False) ∨ p3) ∨ False))) ∧ (True → ((p2 ∧ p4) ∨ True))) ∨ (p3 → (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354099493252034678425636709125 : (p4 → (p5 → ((p3 ∨ (p5 ∨ ((False → p3) → ((p5 ∧ p1) → ((p5 → (p2 → False)) → False))))) → ((True → p1) ∨ ((p5 ∧ p5) → p5))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_559735952406228522859754304233 : (((p4 ∨ (((((((False ∧ p4) → ((True ∧ p5) → p1)) → p1) → p3) ∨ p1) → ((p5 → p1) ∨ p4)) ∨ (True ∨ ((p3 → p2) ∧ False)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_701275668982104574578042268761 : ((((((p3 ∧ ((p5 ∧ p4) ∧ p5)) ∧ False) → (p4 ∧ True)) ∧ ((p1 ∧ ((p2 ∨ p2) ∧ (p1 → p5))) ∧ (p4 ∨ ((p4 ∧ True) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167450926984969653699784916331 : (((p4 ∨ (p1 ∨ (((p1 ∨ (False ∧ ((p1 ∨ (False ∨ p2)) → p1))) ∧ p5) → p3))) → p2) → (False ∨ ((p3 ∨ True) → (p1 → (p2 ∨ False))))) := by
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
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ (p1 ∨ (((p1 ∨ (False ∧ ((p1 ∨ (False ∨ p2)) → p1))) ∧ p5) → p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h8 : (p4 ∨ (p1 ∨ (((p1 ∨ (False ∧ ((p1 ∨ (False ∨ p2)) → p1))) ∧ p5) → p3))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h9 := h1 h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694674083778828454692209331380 : ((((False ∨ (p2 ∨ (p5 ∧ ((True ∨ p3) → ((p3 → (p2 → p2)) ∨ p5))))) ∨ ((p4 ∨ (p3 → p3)) → (False ∧ (p1 ∧ (True ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190607065089487048156777563547 : ((((p2 ∨ p2) → (p1 → ((True ∧ True) ∧ p2))) → p2) ∨ ((p1 ∧ (False ∧ (p2 ∧ (p2 → ((False ∧ p5) → False))))) → ((p2 ∧ False) ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201954685961999778267855062044 : (((p4 ∨ ((p3 ∧ False) → True)) ∨ p3) ∧ (p5 ∨ ((p2 ∧ p3) ∨ (p1 ∨ (False ∨ (p5 → (True ∧ ((p2 ∨ (p2 → p2)) → (False → p5))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304778961334594394427444824597 : (p1 ∨ ((p5 ∨ ((p2 ∧ False) ∧ ((p3 ∨ (p2 ∧ (p2 ∧ p3))) → ((p4 ∨ ((p1 ∧ True) ∨ p3)) → ((p5 ∧ True) ∨ p2))))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119524251349823234682969579539 : ((p5 → ((p1 ∧ ((((((((p1 ∧ p3) ∨ p3) ∧ p4) ∨ p2) ∧ p5) ∧ (p4 → (p5 ∧ (p4 → p1)))) ∨ False) ∧ p3)) ∨ p2)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241612735064799991103422533557 : ((False → p4) ∧ ((p3 ∧ p3) → (((p2 → ((True → ((p3 ∨ p1) → ((p1 → (p5 ∧ True)) → (p2 ∧ p1)))) ∧ p3)) ∧ p2) ∨ (p4 ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50211402580961001082139759931 : (((((p3 ∨ (((((p2 → (p5 → True)) ∨ True) ∧ p5) ∨ (p2 → False)) ∨ True)) → (False ∨ True)) ∨ p1) ∨ (p4 → (p5 → (p2 → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686363222641459127514523842341 : (((((p5 ∨ (False ∨ ((True ∨ False) ∨ p5))) → (((((p3 ∨ True) ∨ p4) ∨ p3) → p3) ∧ False)) → ((((p3 ∨ p2) ∧ p2) ∧ p5) ∧ p4)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ (False ∨ ((True ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p5 ∨ (False ∨ ((True ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ (False ∨ ((True ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p5 ∨ (False ∨ ((True ∨ False) ∨ p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336420747522478124238502773577 : (p1 → ((False ∨ (((p2 ∧ (p4 → True)) → p4) ∨ (p2 → ((p3 ∧ (False ∨ (p2 ∧ ((((False ∧ p2) → p4) ∧ p1) ∧ p5)))) ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193901433911109303457119991754 : ((p1 ∨ (((p5 ∧ (p3 ∨ (p5 ∧ p3))) ∨ False) ∧ p3)) → ((((True ∧ False) ∨ p3) → (p3 → ((p2 ∨ (False ∧ (p4 ∧ p4))) ∨ p2))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
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
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321705147305209006686280478652 : (p4 ∨ (p4 → (True → ((((p5 ∨ (p2 ∧ (p1 → p4))) ∨ False) ∨ ((True ∧ ((((p4 ∧ p5) ∧ p5) ∨ False) ∨ p4)) → False)) ∨ (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748659310829053149227846224073 : ((((p3 → p3) → (((p2 ∨ (((p4 ∨ (False ∨ (p3 → ((p1 → False) ∨ p5)))) → True) → (p2 ∨ p4))) ∧ ((p5 ∨ True) ∧ p3)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177864519821736990814362623236 : (((((p1 → False) → (p5 → ((False ∧ p3) ∧ (p4 ∨ p5)))) ∨ p4) ∨ p2) ∨ ((p4 ∧ (((p1 → p2) ∨ p3) → (p1 ∨ (False → p3)))) → p4)) := by
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
theorem thm_5_vars_187156552579103131418248730939 : (((p2 → p5) ∨ (((True → p2) ∧ (p4 ∧ (p3 → p4))) ∨ p3)) → (((True → p4) ∧ ((False ∨ (((True ∧ p5) ∨ p5) ∧ p2)) ∨ p3)) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
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
theorem thm_5_vars_621599623988633301925358125786 : ((((False ∧ (((p5 → True) ∧ True) ∧ (p1 → (p2 → ((p4 ∨ p5) ∧ ((p5 → (((p4 → p2) → (p4 ∧ p3)) → False)) ∧ p1)))))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_325137811052954913464878790958 : (p5 ∨ (True ∧ ((((p2 ∨ p2) → (p4 ∨ ((False ∧ (p3 ∨ True)) ∨ (p5 ∨ ((False → False) → ((p4 ∨ p1) ∧ p5)))))) → p2) ∨ (p2 → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755886703574795287961368619332 : (((p1 ∧ ((((False → (((p3 ∧ p2) ∧ (((p1 ∧ True) ∧ p1) → True)) → (True ∧ (p3 ∧ (True → True))))) → (p4 → p2)) → p3) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_820126965383931149098991420591 : (((((p3 → (p2 ∧ ((((((p1 ∧ (p2 ∨ p2)) ∧ p5) ∨ True) ∨ (p1 ∨ p3)) ∨ (True → False)) ∧ p2))) → ((p5 ∨ p1) ∧ p4)) ∧ p2) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p3 → (p2 ∧ ((((((p1 ∧ (p2 ∨ p2)) ∧ p5) ∨ True) ∨ (p1 ∨ p3)) ∨ (True → False)) ∧ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7764455967551686370121427420 : ((((((((((False ∧ False) ∨ p1) ∧ True) ∨ False) → (True ∨ ((True ∧ (p4 ∧ p5)) ∧ p1))) → p5) ∨ (p2 ∧ (p3 → p1))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785750574822337007373715432326 : (((p4 ∨ (((False ∨ (p4 ∨ p5)) ∧ (((False ∧ p4) ∧ (p3 ∨ (((p3 → (p2 → (p3 ∨ False))) ∧ True) ∧ p3))) → (p3 ∧ p1))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195774226413105411749505326576 : (((False ∧ p4) → (((p3 → False) ∨ p1) ∧ p3)) ∧ ((((p5 → ((p3 ∨ p3) → p5)) ∧ ((False ∧ (p1 ∧ (False ∧ p1))) → p5)) → p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41708012894341767381536443332 : ((((p3 ∧ ((p3 ∨ True) ∧ (p4 ∧ p3))) → (True ∧ ((p2 ∨ (((p1 ∨ (((p2 → False) ∧ p2) ∧ p4)) ∨ True) ∨ True)) ∧ p5))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136657387466730686265451170461 : (((p2 ∧ (p3 ∨ p5)) → ((((((True → False) → (p2 ∨ (p3 → True))) ∧ (p5 ∨ True)) ∧ p1) ∨ p4) ∨ (p3 → p2))) ∨ (p1 ∧ (p5 ∧ p3))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614619464418896622294931182896 : (((((p1 ∨ ((p5 ∧ ((False ∨ (p2 ∨ (True → ((p4 ∧ p2) ∨ (p2 → p3))))) ∨ p5)) ∧ True)) ∧ ((p3 ∨ (p1 ∧ p4)) ∨ p2)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_711671136075102162315380751930 : ((((p4 → (p1 ∧ (p5 ∧ (True ∧ p5)))) ∧ (((p1 ∨ p2) → ((False → p3) → (p5 → (p3 → p3)))) ∨ (False ∧ ((p1 ∧ True) → True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351690131123684944343846221156 : (p4 → (((p5 → ((False ∨ (p4 → ((p3 ∧ p2) ∨ p4))) ∨ (p1 ∨ p1))) ∧ True) ∧ (False ∨ (((((p1 ∧ True) ∧ True) ∧ p1) ∧ p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352024110583506194270187413040 : (p4 → (((((p3 ∨ False) ∨ (False ∨ p4)) ∨ True) ∨ False) → (p4 ∧ ((False ∨ p1) ∨ (((p3 → ((p5 → p4) ∨ p3)) → (p5 → True)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h7 =>
          -- False on the left can always be used.
          apply False.elim h7
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h1
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h2
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h17 =>
          -- False on the left can always be used.
          apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h22 =>
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_176387138343547504502196394680 : (((((p5 ∧ False) ∨ (p1 ∧ (True → True))) ∨ True) ∧ (p1 ∨ (p2 ∨ True))) ∧ (((p2 → (p1 → True)) ∨ False) ∨ (p5 ∨ ((p5 → p2) ∧ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117202661044014534299659657015 : ((True ∧ ((p1 ∨ (False ∧ ((p1 ∨ p2) ∧ (p3 ∨ (True ∨ False))))) ∨ ((p1 → p5) ∧ ((p5 ∧ p5) ∨ (p5 → (p5 ∨ p4)))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191288250113098521721094574465 : (((p5 ∨ p3) ∧ ((p1 ∧ (False ∨ p5)) ∨ (p3 ∨ p4))) ∨ (p3 → (((p5 → ((p5 ∨ (p4 ∨ p4)) ∨ ((p1 ∧ False) → p2))) ∧ p3) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116247152256425498929901659670 : ((((False → p3) → p1) ∨ ((((p4 ∨ p1) ∨ p1) ∧ (((p4 ∨ ((p4 ∧ p4) ∧ (p5 → p3))) → p1) → (p3 ∧ p4))) ∧ p4)) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337398172337104437985903523193 : (p1 → ((p1 → ((p1 ∨ (((p2 → p1) ∨ ((False → p3) ∧ p4)) ∧ (True ∨ p1))) → (((False ∧ p3) → False) → p4))) ∨ (p4 ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69040167911843514272499795023 : ((p5 → ((((((True → False) ∧ ((p4 ∨ p3) → p1)) → (False ∧ True)) → p2) ∨ (p3 ∨ (p4 ∨ ((p1 → (p2 → p4)) ∨ p3)))) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68173983025764743700363244185 : ((p3 → (((False ∧ ((((p5 ∨ (p5 ∧ (False ∨ True))) ∨ p5) → ((False ∨ (True → ((True → True) → False))) ∧ False)) ∨ p5)) ∧ p1) ∨ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779539792385835989786754705012 : (((p2 ∨ (((p4 → p2) ∧ (((p5 ∧ (((p5 → (p1 ∧ False)) ∨ (True ∨ (p5 → (False → (p5 ∨ p2))))) ∨ p1)) ∧ p2) ∨ p5)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219513963525077209024256440110 : ((p5 ∨ ((p3 → p4) → p4)) → ((p1 ∨ ((((False ∨ (True → p5)) ∨ True) ∧ ((p1 → p3) ∧ (False → p1))) ∧ (p4 ∧ True))) ∨ (False → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119582824469965506544775677353 : ((p5 → ((True → p1) ∧ (((p3 ∨ False) ∨ (((False ∧ ((p4 ∨ (p1 ∧ p1)) ∨ p4)) → (p4 → True)) → (p4 → p3))) ∨ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171634740973481886065929000238 : ((((False → p3) ∧ ((p1 ∨ ((p4 ∨ (p2 → (p4 ∧ p4))) ∧ p1)) ∧ False)) ∨ p1) ∨ ((p5 → ((p4 ∧ False) → (p4 → (False → p4)))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624663883168105425223398273580 : ((((p4 ∨ ((p5 → p1) → (p3 ∨ (True ∧ (((p1 → (False → p2)) ∨ p5) → ((p3 → p1) ∨ (p3 ∧ (p5 ∧ (p5 → True))))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_718478614742052615482373529859 : (((((p5 ∧ (p3 → p4)) → p2) ∨ (((((False ∧ ((p4 → p2) ∧ p4)) → False) ∧ False) ∧ p5) ∨ ((p3 ∨ (False → False)) ∧ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340917152700319500712800390385 : (p2 → ((((p3 → (False ∨ ((p5 ∧ True) ∨ p5))) ∨ p4) → ((p4 ∧ (False → (False ∧ ((p4 ∧ ((p4 ∨ p2) → p2)) ∨ p5)))) ∧ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_220320719283044127524380200396 : (((True ∨ p5) ∧ True) ∧ (((p2 ∧ (p3 ∨ (p4 ∨ False))) → ((False ∧ (p4 ∨ False)) ∨ p3)) ∨ ((p4 → True) ∧ ((p4 ∧ p4) → (p4 ∨ p1))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114616607691997207470735814697 : (((p4 → ((((p3 ∨ (p4 ∨ (False ∧ True))) ∨ (p4 → (p4 ∨ p2))) ∨ p2) → p1)) ∧ ((p2 ∨ ((p4 → p4) → False)) ∨ p5)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41349175301540045834578174610 : ((((p5 ∧ (((((p1 ∧ p2) → p1) → (p4 → (p2 ∨ (p1 ∧ p1)))) ∨ p4) ∧ p1)) ∨ (True → (((False ∨ p5) → p1) → False))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168295060534066114887219723255 : (((False ∨ p2) ∧ (p1 ∧ ((p1 ∨ (False ∨ ((False → False) → False))) ∨ ((p2 ∨ p2) ∧ p2)))) → ((p3 ∧ ((True → (p1 ∧ True)) → p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h5
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249957027751732528933503445613 : ((True → p2) ∨ ((((((p4 ∨ p3) → p3) → (((((False ∨ p4) ∧ p2) ∧ (p1 → p2)) ∨ p4) ∨ ((True ∧ p3) → p3))) ∨ p5) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150330751570197934010875678491 : ((p5 → (((((False ∧ ((False ∨ False) → (p5 ∨ p2))) ∧ (p1 → (p2 → (False ∨ p4)))) ∧ False) ∨ p4) ∨ p4)) ∨ (p1 → (p4 → (p3 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229646600829031094864331820028 : ((p3 → (p4 ∨ p2)) ∨ (p5 ∨ ((((p4 ∨ ((True ∨ p5) ∧ p4)) ∨ False) ∧ p4) ∨ ((p1 → ((True ∨ p4) → ((False ∧ True) ∧ p5))) → True)))) := by
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
theorem thm_5_vars_208040640146298658586894175517 : (((p3 ∧ (p5 ∨ p5)) ∨ (p4 → p5)) → ((p3 ∧ ((p5 ∨ p1) → p4)) → (p4 → (((p4 ∧ ((p3 → True) → True)) ∧ (True → p1)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217935964010553089343319231090 : (((True ∧ p4) ∧ (True ∧ p4)) → ((((p2 → True) ∧ (False ∨ ((p2 ∧ ((False ∧ (((p3 ∧ p5) → p2) → p1)) ∨ p1)) ∨ p1))) ∨ p4) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337128841663830527694378925454 : (p1 → ((p5 ∧ (((p4 ∧ ((True ∧ p5) ∨ (False ∨ (((p4 → False) ∧ p4) → p2)))) ∧ (False → p4)) ∧ ((p2 ∨ p5) ∨ p1))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149212717737133134400663655970 : (((False ∧ p4) ∨ (p1 ∨ (((p4 ∨ p1) ∨ p5) ∧ ((p3 → (p5 ∧ (p2 ∨ (False → p1)))) ∧ (p5 ∨ False))))) ∨ (p4 → (p4 ∨ (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43046252830539904872152289658 : (((((p5 ∨ (((((p3 ∨ (p5 ∧ False)) ∧ (p4 ∧ p2)) → p3) → True) ∧ ((p1 → (p4 → p3)) ∨ (p4 ∧ p5)))) ∨ p2) ∧ p3) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175162466325531919031177317912 : ((True ∨ ((p5 ∨ (p2 → (((((p2 → p5) ∨ True) ∧ p2) ∧ p3) ∧ False))) ∨ p2)) → ((False ∨ p5) ∨ (p2 → (p3 → ((p2 ∨ True) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303105076129295185587693609569 : (False ∨ (p3 → ((((p3 ∨ (True ∨ False)) ∨ ((True ∧ (p5 ∨ (False ∨ (p1 → True)))) ∨ p5)) → (p5 → (((p2 ∧ True) ∧ p4) ∧ p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148323428645016860566094997630 : (((p4 → (((((False ∨ p1) ∨ p1) ∨ (p3 → False)) ∨ p1) → (False ∧ (False → p1)))) → ((p3 ∨ p3) → p5)) ∨ ((p5 ∧ p1) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228916477409730489637568895296 : ((p4 ∨ (False ∨ p3)) ∨ (p5 → (p2 ∨ ((p3 ∨ True) ∧ (p2 ∨ ((True ∧ p4) → ((False ∧ ((p3 ∨ (True ∧ p4)) ∧ True)) ∨ (p4 ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55868540264070709733419977136 : (((p5 ∧ (p1 ∨ (p1 → p1))) ∧ ((p5 ∧ (True ∧ ((p4 → ((True ∨ (False ∨ (p1 ∨ True))) ∧ (False ∧ p1))) ∨ p1))) ∧ (p2 → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138023449749060448226339025782 : ((True → (((p5 ∧ p1) → (p1 ∨ ((False ∨ ((p5 → p4) → ((p1 → (p2 ∧ p3)) ∨ (False → p3)))) ∧ True))) → p5)) ∨ ((p4 ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



