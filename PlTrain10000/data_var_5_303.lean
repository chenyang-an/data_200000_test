variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227855221504408233052480060294 : ((p2 ∧ (False ∨ p5)) ∨ (p4 ∨ ((p2 ∨ (((p5 ∧ (((p4 ∨ True) → p5) ∧ (p1 ∨ p5))) ∧ False) → ((p2 ∧ p5) ∧ (p2 ∨ p2)))) ∨ p4))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h10 := h1.left
  let h11 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Conjunctions on the left can always be decomposed.
  let h14 := h13.left
  let h15 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- False on the left can always be used.
    apply False.elim h11
  case inr h17 =>
    -- False on the left can always be used.
    apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h18.left
  let h21 := h18.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h24 =>
    -- False on the left can always be used.
    apply False.elim h19
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319026554417886815773558339042 : (p4 ∨ (((False ∨ (((True → (p4 → ((p1 ∨ (False ∨ p3)) → p2))) ∨ (False ∨ p5)) → (False ∨ p3))) ∧ p3) ∨ (False → ((True ∨ p2) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625856843299256454106709749275 : ((((p2 → (((p1 ∧ ((((p3 ∨ True) ∧ p4) ∨ False) → True)) → (p2 → ((p1 → (p1 ∨ (False ∧ (p2 ∨ p4)))) ∧ p5))) ∧ p1)) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125905782608469877124660627185 : (((p5 ∧ True) → ((p2 ∨ (p2 ∨ ((True ∧ (p3 ∧ (((p3 → p5) → p1) ∨ (p5 ∧ (p4 ∨ p2))))) → p3))) ∨ (p1 ∧ False))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675969011716456902119387916981 : (((((((p5 ∨ (p1 → p2)) ∧ (False → True)) ∨ False) ∧ ((((p1 → p1) ∨ False) ∧ p1) ∨ (p2 ∧ p2))) ∧ ((p3 ∧ p3) ∧ (p1 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231463274909873786970362192733 : (((p2 → p5) ∨ p3) → (((p4 ∨ (True ∧ ((p1 ∨ (p5 ∨ ((p2 → (False ∧ p3)) ∧ p4))) ∨ p4))) ∨ True) ∧ ((True ∨ p5) ∨ (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356372734862127494133383441247 : (p5 → (((p2 ∨ ((((((p4 → p2) ∨ p2) ∧ p4) → False) ∨ p2) ∨ p5)) ∧ p3) → (True → (((((p5 → p2) ∨ True) ∨ p4) ∧ p3) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
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
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h18 =>
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47041839177501374107515638752 : ((((((((False ∨ False) → p2) ∧ (p4 ∨ p2)) ∨ True) ∧ ((True → (p4 → p5)) → (p3 → (p5 ∨ False)))) ∧ (True ∧ p2)) ∨ (p5 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355639707287837975189020143718 : (p5 → ((p3 → (((((p1 ∨ (p4 ∧ p3)) → (p5 → p4)) ∧ (False ∧ (p2 → p2))) → ((p4 → (p1 ∧ False)) ∨ p5)) → p1)) ∨ (p5 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60696644615924658398144522163 : ((True ∧ ((((p2 ∧ (False ∨ p3)) ∧ (True ∨ p1)) ∨ (p3 → p2)) ∨ ((p4 ∨ ((False ∨ False) ∧ p3)) ∨ (((p4 ∨ True) ∧ False) → True)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264961639260008790548747390680 : (True ∧ ((p2 ∨ p4) → (((p3 → p1) ∧ ((p5 ∨ p3) ∨ ((((p2 ∧ ((p5 ∨ (p1 → p2)) ∨ (p5 ∧ p3))) ∨ False) → p3) ∨ p2))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_68210533506493487609200617679 : ((p3 → ((p5 → (p3 ∧ ((((p1 → ((p3 → (p1 ∧ (p3 ∧ ((p5 ∧ p3) → p1)))) → p5)) → p3) ∧ (p2 ∧ p1)) ∨ p4))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608825962759125305267731355677 : (((((((((True ∨ (p2 → (p5 ∨ ((True ∧ p5) → False)))) ∨ (p1 ∨ p2)) ∧ p1) ∨ p1) ∧ (((True ∨ True) ∨ p3) → p2)) ∨ True) ∨ p5) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_215854103872787461086358960068 : ((p2 ∨ (p4 ∧ (p1 → p1))) ∨ ((False ∧ (((p1 → (False ∨ (False → ((False ∧ p4) ∨ ((True ∧ (p2 ∧ p2)) ∨ True))))) → False) ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315421548463238813168205325231 : (p3 ∨ ((False ∧ (True ∨ p1)) ∨ ((p4 ∨ ((p1 ∨ ((p4 ∧ (((p2 ∧ p1) ∧ (p3 ∨ p1)) ∨ False)) → p3)) ∨ (True ∨ p3))) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
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
theorem thm_5_vars_147161458538082362662532432750 : (((p5 ∧ (((p2 ∨ p1) → (p3 ∨ (((p2 ∧ ((p4 ∧ p1) ∨ True)) ∧ p3) → (p1 → False)))) ∧ True)) ∧ p4) ∨ (((False → p5) ∧ p1) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147378178232264242082947670526 : (((((p2 ∧ (False → p1)) → ((p3 ∨ p3) → (p3 ∧ p1))) ∧ ((p4 ∧ (True → (p4 ∧ p1))) ∨ p5)) ∨ p1) ∨ (p4 → (p2 ∨ (True ∨ p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47695855903420373939061811339 : ((((p5 ∨ (((p4 → p2) → p4) ∨ (p2 ∨ ((False ∨ ((((True ∧ False) ∧ p5) → False) ∨ False)) ∨ (p1 ∨ p5))))) ∧ True) → (p1 ∨ True)) ∨ p5) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- False on the left can always be used.
            apply False.elim h11
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h14 =>
              -- False on the left can always be used.
              apply False.elim h14
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112777434333971901237317510703 : ((((False ∨ (True → ((False ∧ p5) ∧ (True ∧ True)))) ∧ ((p1 ∧ ((p4 → p3) ∨ (((p3 ∧ p4) → p4) ∨ p2))) ∨ p5)) → p5) ∨ (p5 ∨ p3)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h10 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h11 := h5 h10
        -- We need to get the left conjuct of h11 based on <expert-advice>.
        let h12 := h11.left
        -- We need to get the right conjuct of h12 based on <expert-advice>.
        let h13 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h16 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h17 := h5 h16
          -- We need to get the left conjuct of h17 based on <expert-advice>.
          let h18 := h17.left
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h20 =>
          -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h5, we can now drive its conclusion.
          let h22 := h5 h21
          -- We need to get the left conjuct of h22 based on <expert-advice>.
          let h23 := h22.left
          -- We need to get the right conjuct of h23 based on <expert-advice>.
          let h24 := h23.right
          -- One of the premise coincides with the conclusion.
          exact h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166421055071929310890440978902 : ((p1 ∨ ((((p3 ∧ (p1 ∨ p1)) → p1) ∧ (p4 ∨ p2)) → (p2 ∨ (p5 ∧ (p5 ∨ p3))))) ∨ ((False ∧ p2) → (p2 ∧ ((False → p5) ∧ False)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304677816737538879525277167928 : (p1 ∨ ((((((p2 ∧ ((p4 ∧ False) → p1)) → p1) → (False ∧ p1)) ∨ ((p1 → p4) ∧ ((p4 ∧ p2) ∨ (p3 ∧ False)))) ∧ p4) ∨ (p4 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339771131645180090169740516687 : (p1 → (p4 ∨ (p4 ∨ (p2 → ((p5 ∨ (p3 ∨ p5)) ∨ (((False ∧ p5) ∨ (p5 → ((p4 ∧ p1) ∧ ((p4 ∧ False) ∧ (p5 ∨ p3))))) ∨ p1)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747574722869170270080259756482 : ((((True → p3) → ((((False ∨ p3) ∨ p1) ∧ p4) ∨ ((p3 → ((True ∧ p4) → (((p4 → ((p3 ∧ p5) → p5)) → p2) ∨ p4))) ∨ p4))) ∨ p2) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208881224508254265985537481964 : ((p4 ∧ (p4 ∧ ((True ∨ p3) → p3))) → (((p4 → p1) ∨ p5) → (p2 ∨ ((True → (p3 → ((((True → False) ∧ p3) ∧ p1) ∧ True))) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h1.left
    let h13 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h17 : (True ∨ p3) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h18 := h15 h17
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h19 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h19
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39204125797611889072668276462 : (((True ∧ (((True → (p5 ∨ (p4 ∨ (((p1 → (False ∧ p4)) ∧ p4) ∧ p5)))) ∨ (True ∧ (p4 ∧ ((True → p4) → p5)))) → p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89024986383594788101638269489 : ((((True → False) ∧ p1) ∧ (((p2 ∨ ((p2 → p1) ∧ p1)) ∧ p3) ∨ ((p3 → (p1 ∧ ((((p1 ∧ True) → True) ∨ p3) → p3))) → True))) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h17 := h4 h16
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316911005069826366250741923359 : (p3 ∨ (p2 → (((((((((p1 ∧ ((p5 ∨ (False → p4)) → (p5 → p3))) → p4) → p4) → True) ∨ (p2 ∧ True)) ∨ p2) → p3) ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52932867795631418687484380513 : (((((p2 → False) ∨ (p1 ∧ ((True → False) ∨ (p4 → p4)))) ∧ p5) ∧ ((p3 ∨ ((p5 ∨ p2) → p3)) ∧ (((p4 → True) → p3) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123343377191852087011269089997 : ((((True → False) ∧ (((p2 ∧ p4) ∧ (True ∨ p4)) ∨ (((False ∨ p1) → True) ∨ (p4 → p5)))) ∨ (True → (False ∧ (p2 ∨ p5)))) → (p1 → False)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h11 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h13 := h4 h12
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h16 := h4 h15
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- False on the left can always be used.
        apply False.elim h23
  case inr h24 =>
    -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
    have h25 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h24, we can now drive its conclusion.
    let h26 := h24 h25
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- False on the left can always be used.
    apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259327638680330595081606840122 : ((False → p2) → ((((True ∧ (p2 → ((p3 → ((p3 ∨ p1) ∨ False)) ∧ (p2 ∧ p4)))) ∨ p4) ∨ (True → True)) ∧ (p1 → ((True → p4) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341976243333035391545167063260 : (p2 → (((p1 ∧ ((((p3 → p5) → (p4 → p3)) → (p5 ∨ (p2 ∨ ((p2 ∨ p5) ∨ p1)))) ∧ (p4 ∨ p5))) → p4) ∨ ((p5 ∧ False) → p3))) := by
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
theorem thm_5_vars_66829224184550407174906603006 : ((True → (p1 → ((((p5 ∧ ((p3 ∧ p3) ∨ ((p2 → (p3 ∨ True)) → (False ∧ (False ∧ p3))))) → True) → ((p4 ∧ p2) → p5)) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686263285510129535875675300047 : ((((((p1 ∨ (False ∧ (p2 → (True → p2)))) ∨ p2) ∨ (p3 → (((False ∧ p1) → False) → p2))) → (((p2 ∨ (p5 ∨ p2)) ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205068443819026330640806836925 : (((p3 → (False ∨ (p4 → True))) → False) ∨ ((p2 → (p5 ∨ (((((True ∧ p3) ∨ ((p3 → p5) ∨ p4)) ∧ p1) ∧ (p3 → True)) ∧ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149563709941884779235966418787 : ((p2 ∧ ((True ∧ p1) → (p4 → (False ∨ (p3 ∨ (p2 ∧ (((True ∨ False) → (False ∨ (p3 → p4))) ∧ False))))))) ∨ (True ∨ (False ∧ (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165945235315283076035913689078 : (((p2 ∨ True) ∧ ((((p5 ∧ p1) ∧ False) ∨ p5) ∨ (True ∨ (p5 ∧ (p3 ∧ (p5 ∧ p4)))))) ∨ ((((False ∧ (p3 ∧ p2)) ∨ True) → p5) ∧ p2)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205937094682433509912634440437 : ((False ∧ ((p5 ∧ p2) ∨ (p3 ∨ p3))) ∨ ((((False ∨ (p4 ∨ (p1 ∧ (True ∨ p1)))) ∨ True) ∧ (False → p1)) ∧ (((p5 ∨ p1) ∨ True) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182754934188494308890420602477 : (((p1 ∨ ((p3 ∧ False) ∨ p5)) ∨ ((p3 → p5) → (p4 ∨ True))) ∧ (p2 → (((p1 → p2) ∨ p5) ∨ ((((p5 ∨ True) → p3) ∨ p3) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326021204130249632216939086002 : (p5 ∨ (True → (p2 ∨ (((p3 → p2) → (((((p2 → False) ∧ p4) ∨ (False → p4)) ∧ (((True ∧ p3) → (p3 ∨ p5)) → p5)) → p5)) ∨ p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : ((True ∧ p3) → (p3 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h9
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h14 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h15 : ((True ∧ p3) → (p3 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h19 := h5 h15
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637606508045736466862096722971 : ((((((False → p1) → (p1 ∧ (((p2 ∧ p1) ∧ p2) ∧ p5))) ∨ (((p4 ∨ (p5 ∧ True)) → p5) ∧ (p3 ∨ (True → (p5 ∨ p2))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165494450570864261588768174867 : ((((p5 ∨ p3) → (((False ∧ p1) ∧ p1) ∨ (False → p3))) ∨ (((p4 ∨ p2) ∧ p3) → p4)) ∨ (((((p4 → False) → p1) ∧ p4) ∧ p4) ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_349999064205208130777386948030 : (p4 → ((((p1 ∨ (p2 → p5)) → ((p2 ∨ (p2 ∨ ((p4 ∨ p4) → ((p4 ∧ p4) ∨ (p2 ∨ p5))))) ∧ ((False ∧ p1) ∧ False))) ∨ p4) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_427640017223490910379645918009 : (((((((((((p5 ∧ p1) ∨ p5) ∨ ((p3 ∧ (p3 ∨ p5)) ∨ False)) → p1) → (p3 ∧ p4)) ∨ (p5 → p4)) ∨ True) ∨ True) ∨ (p2 → p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351301216310673462198388697677 : (p4 → (((p1 ∧ (((p2 ∧ ((p2 → p2) ∨ p1)) ∨ p1) ∧ (True ∨ p2))) ∧ (((p2 ∧ p4) ∨ p4) → (p4 → False))) → (p2 ∧ (p2 ∧ p2)))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h19 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h20 : ((p2 ∧ p4) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h21 := h4 h20
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h23 := h21 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Conjunctions on the left can always be decomposed.
  let h29 := h28.left
  let h30 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h29
  case inl h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h36
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h38 =>
        -- One of the premise coincides with the conclusion.
        exact h32
      case inr h39 =>
        -- One of the premise coincides with the conclusion.
        exact h39
  case inr h40 =>
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h41 =>
      -- We want to use the implication h26 based on <expert-advice>. So we show its premise.
      have h42 : ((p2 ∧ p4) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h26, we can now drive its conclusion.
      let h43 := h26 h42
      -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
      have h44 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h43, we can now drive its conclusion.
      let h45 := h43 h44
      -- False on the left can always be used.
      apply False.elim h45
    case inr h46 =>
      -- One of the premise coincides with the conclusion.
      exact h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h2.left
  let h48 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h49 := h47.left
  let h50 := h47.right
  -- Conjunctions on the left can always be decomposed.
  let h51 := h50.left
  let h52 := h50.right
  -- Disjunctions on the left can always be decomposed.
  cases h51
  case inl h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h53.left
    let h55 := h53.right
    -- Disjunctions on the left can always be decomposed.
    cases h55
    case inl h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h57 =>
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h58 =>
        -- One of the premise coincides with the conclusion.
        exact h58
    case inr h59 =>
      -- Disjunctions on the left can always be decomposed.
      cases h52
      case inl h60 =>
        -- One of the premise coincides with the conclusion.
        exact h54
      case inr h61 =>
        -- One of the premise coincides with the conclusion.
        exact h61
  case inr h62 =>
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h63 =>
      -- We want to use the implication h48 based on <expert-advice>. So we show its premise.
      have h64 : ((p2 ∧ p4) ∨ p4) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h48, we can now drive its conclusion.
      let h65 := h48 h64
      -- We want to use the implication h65 based on <expert-advice>. So we show its premise.
      have h66 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h65, we can now drive its conclusion.
      let h67 := h65 h66
      -- False on the left can always be used.
      apply False.elim h67
    case inr h68 =>
      -- One of the premise coincides with the conclusion.
      exact h68



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39196109719808218229800633060 : (((True ∧ (((p4 → ((False ∧ p5) ∨ (((((p3 ∧ p5) → False) ∨ p1) ∨ (True ∨ ((False ∧ True) ∧ p4))) → p2))) → p5) ∧ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116448138363460181184669284322 : (((p5 → (False → p1)) → ((p5 ∨ True) ∧ (((False → ((((True ∧ (p3 → p1)) → (p1 ∧ p3)) ∧ p2) → p4)) ∧ p1) ∨ p4))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88120198123794205174805204306 : ((((p3 → (p1 → True)) → False) ∧ (((p3 ∧ ((True ∧ p3) ∨ False)) ∨ p1) ∧ (p5 ∨ ((p2 ∧ (p3 ∧ p3)) → (False → (p1 ∧ p4)))))) → p2) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h13 : (p3 → (p1 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h13
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : (p3 → (p1 → True)) := by
          -- Implications on the right can always be decomposed.
          intro h19
          -- Implications on the right can always be decomposed.
          intro h20
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h21 := h2 h18
        -- False on the left can always be used.
        apply False.elim h21
    case inr h22 =>
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h25 : (p3 → (p1 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h26
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h28 := h2 h25
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h30 : (p3 → (p1 → True)) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- Implications on the right can always be decomposed.
        intro h32
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h33 := h2 h30
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185095101385471718838218815777 : (((p5 ∨ p3) ∨ ((((True ∧ p4) ∨ True) → (False ∨ True)) ∧ p2)) ∨ (p5 ∨ (p1 ∨ (p4 → ((True ∨ (p3 ∨ (False ∨ p1))) ∨ (p3 → True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_48617258585752900546594280448 : (((((p1 ∧ p2) → (p5 ∨ ((((p3 → (p3 ∨ True)) ∧ ((True → True) → p5)) ∧ p2) → True))) → (p2 ∨ p4)) ∧ ((True ∧ p4) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114976635356971650894177079050 : ((((p3 → (((p3 → (p5 ∨ (False → True))) ∧ False) ∨ p2)) ∧ p5) ∧ ((p4 → (p1 ∨ False)) ∧ (((p1 ∨ p2) → True) ∧ p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804875766012701965731736326950 : (((p3 → ((p4 → p1) ∧ ((p3 ∧ ((True ∨ (p2 ∧ p1)) ∧ (p3 → ((p2 ∧ (True ∨ p1)) → p4)))) ∧ ((p4 ∨ (p3 → p3)) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301530637355633303298369305288 : (False ∨ (((p3 ∧ p2) ∨ p5) ∨ (p3 ∨ ((p2 → ((p3 ∨ p3) ∨ (p4 ∨ (p4 → (p2 → ((True → (p3 → p4)) → p2)))))) → (p4 → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178592487382892251207166798280 : ((((p5 ∧ (p5 ∧ (p3 ∨ p3))) → p2) ∨ ((False ∧ (p5 ∨ p3)) ∧ p2)) ∨ (((p2 ∨ p2) ∧ (((p1 ∨ p1) ∧ p2) ∧ False)) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116365521816695890070664031716 : ((((p2 ∧ p3) → p1) → (((p5 → (p2 → (p4 ∧ False))) ∨ False) → (((((True ∧ (p1 → p3)) → p4) ∧ p5) ∨ True) ∨ p1))) ∨ (p2 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715713299093894675303995787641 : ((((((p5 ∨ False) ∧ p1) ∨ p4) ∧ ((((p3 → (p2 ∧ ((((p4 ∨ (False ∨ (False ∧ False))) ∨ p2) ∧ p1) → False))) ∧ p5) ∨ True) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245613736116445281447889714725 : ((p3 ∧ False) ∨ (((p3 ∨ p4) ∧ (p4 ∧ False)) ∨ ((True ∧ True) ∧ ((p4 ∧ (True ∨ (p1 ∧ (p1 → (p5 ∧ p1))))) → (p3 → (False → p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789032369667678970363465621658 : (((p5 ∨ ((((p1 → p4) ∧ (True → p4)) ∧ (((True ∧ (p5 → p1)) → ((p5 ∧ False) → (p4 → p4))) → (p5 ∧ p5))) → (False ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156849026387540878304492736909 : (((p4 → (p3 ∨ ((p1 → p4) ∧ ((p3 ∨ (p1 → p2)) ∧ ((True → (False ∧ False)) ∨ False))))) ∧ p3) ∨ ((p2 → p2) ∨ ((p2 → p5) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_95635938145301442899323358887 : ((p5 ∧ (((p4 → False) ∧ (p3 ∧ p4)) ∧ (((p5 ∨ True) ∨ (((p1 ∨ p1) → (((p2 ∧ (p3 ∧ p5)) ∨ p4) → p4)) ∧ p2)) ∨ p4))) → p1) := by
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
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h16 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h17 := h6 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h21 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h22 := h6 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h24 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h23
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h25 := h6 h24
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259554227306938817420544921475 : ((p1 → True) → (((((((((p3 ∨ p2) ∧ p4) ∧ True) ∧ (False ∨ p3)) → p5) → p4) ∨ p3) ∨ (p1 ∨ (((p4 → p5) → False) → True))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185909804472743610034849134736 : ((((p3 → (p3 ∨ (True ∨ p5))) ∧ (p3 → (p4 ∧ p2))) ∧ p2) → ((((p2 → (p1 ∨ p3)) ∧ False) ∨ p3) ∨ (False → ((p2 → False) → p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_392420659576709042442510992407 : ((((((False ∨ p4) ∧ p2) ∨ ((p3 ∨ ((((True ∨ p5) ∨ (p4 ∨ p5)) ∨ p2) → False)) ∨ (True ∨ (((p1 → p5) ∧ p4) ∧ True)))) ∨ p5) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40351195931106170388080708338 : ((((((((p1 ∧ (True → (p3 ∧ p4))) → (p1 → (((p1 ∧ (p2 ∨ p2)) ∧ p3) ∨ (p4 → False)))) ∧ p4) ∨ p4) → p2) ∨ True) ∨ p5) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1470251916950677282899348522 : (((((False ∧ (p5 ∧ p2)) ∨ (p2 ∧ (((p5 ∧ (p3 → (p5 → p1))) ∧ p2) ∧ p4))) ∨ ((False → p2) ∧ p3)) ∨ p1) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114968472071843186529816253523 : (((p3 → (False → (p4 ∧ (((p1 → p5) ∧ False) → (p1 ∧ (False ∨ True)))))) → (((True → False) ∧ p1) ∧ (True ∧ (p1 ∧ p2)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142938908023964674077644210876 : ((p5 ∨ ((p4 ∧ ((True → p5) → p3)) → ((p1 ∧ ((p2 → p4) → p2)) ∧ (p1 ∨ ((p3 ∨ p2) ∧ (True ∨ p5)))))) → ((p3 → False) ∨ True)) := by
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
theorem thm_5_vars_325156859958171192290175189246 : (p5 ∨ (True ∧ ((p3 ∧ (p5 ∧ p2)) ∨ (((((p2 ∧ (p2 → (((True ∨ True) ∧ (p3 ∧ True)) ∧ (p2 → p4)))) ∨ p3) → p3) ∨ True) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54022728343393531865246510645 : ((((((p4 ∨ (p2 ∨ p4)) → p5) → p2) ∧ (p5 ∨ False)) → ((((((p5 ∧ p1) ∧ (p3 ∨ p3)) ∧ p1) ∧ (p3 ∨ p4)) → p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180052237245867713269734791554 : (((p3 ∨ (((p1 ∧ ((p1 ∨ (p3 ∨ p4)) ∨ p5)) ∧ True) ∨ True)) ∨ p2) → (((p5 ∨ (p2 → (p2 ∧ False))) ∨ (True → p5)) ∨ (False → p2))) := by
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
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h13
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h16
              -- False on the left can always be used.
              apply False.elim h16
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h18
              -- False on the left can always be used.
              apply False.elim h18
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661366343944009618332609529044 : ((((((p1 ∧ (p3 ∧ True)) ∨ ((p1 ∨ ((False ∧ (p4 ∧ (p3 ∨ (p3 → p3)))) ∨ (False ∧ p3))) ∧ False)) → (p5 ∧ True)) → (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774913556935770423352472459238 : (((False ∨ ((p1 → ((p4 → p4) ∨ p2)) → (p2 → ((False ∧ (p4 → p1)) ∨ (((p5 ∨ ((False → (p4 → p2)) → False)) → p3) → True))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45272566150487537806773872043 : (((p2 ∧ ((((True ∧ (p5 → (p3 → p5))) → (True → (((False → (p2 ∨ (False ∨ (p4 ∨ p1)))) → p5) ∨ p5))) ∨ p3) → p3)) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115045608495723914203391926859 : ((((p5 ∨ ((((p3 ∧ p3) ∨ p3) ∨ (p4 ∧ p1)) ∧ p4)) ∨ p5) ∨ (p3 → ((p5 ∧ (p2 → (p2 → p5))) ∧ (p4 ∧ True)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40514065227168555417981518799 : ((((p4 ∧ (((((p3 → ((p5 ∨ p3) → False)) ∨ True) ∨ (False ∧ ((p4 ∧ p3) ∧ (p3 ∧ p3)))) ∧ (p4 → False)) ∧ True)) ∨ p2) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148469613690351545082205150989 : (((p4 ∧ (((p2 ∨ p3) → (((p3 → p4) → p2) ∧ False)) ∨ p4)) ∧ ((p2 ∨ ((p5 → True) ∧ p2)) ∨ p2)) ∨ ((p2 ∧ False) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112076331261570193494546721179 : ((((p1 ∧ False) ∨ (p4 ∧ ((((((p1 ∧ ((p4 ∨ (p4 ∨ False)) ∧ (False → True))) ∨ p2) ∧ p3) ∨ p5) ∧ p1) → p2))) ∨ p5) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121128273719510962662761131681 : (((True ∨ (((p3 → (p5 ∨ p2)) ∧ p1) ∨ ((((p2 ∧ p2) → p1) ∨ True) ∧ (p4 ∨ (p5 ∨ (p5 ∨ (p2 → True))))))) ∨ True) → (p1 ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
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
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h15 =>
              -- Disjunctions on the left can always be decomposed.
              cases h15
              case inl h16 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h17 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
        case inr h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690568421005938374984704107047 : ((((((True → (((p2 ∨ (p4 → p2)) ∨ (p1 ∨ True)) ∨ (p1 ∧ p3))) ∧ p5) ∨ True) → ((((p3 → p4) ∧ (p5 ∨ p3)) ∨ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118890588627675151890219348130 : ((True → (p4 ∧ (p1 ∧ (((True ∧ ((p2 ∧ p1) → False)) ∨ p3) ∧ ((p2 ∧ p2) ∧ (((p1 → (False ∧ p5)) → p5) ∧ p1)))))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589902580013871936511482612256 : (((((((((True ∨ True) → (((p5 → p1) ∨ (p1 → p2)) ∧ (True ∧ p1))) ∨ p2) ∨ (p3 → True)) → (p4 ∨ (True ∧ p2))) → p5) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58297693445778937041273968082 : (((True ∨ p2) ∧ (p5 ∨ (p5 → ((True ∨ p4) ∧ (((p1 → (((p2 → p2) → p2) ∧ False)) ∨ False) → ((p2 → (True ∧ False)) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49216833113954160964851428759 : ((((p2 ∨ p2) ∧ (False ∨ (((((p4 ∧ p4) ∧ p2) ∧ p1) ∨ (False ∧ (True → ((True ∧ p2) ∨ p5)))) ∨ True))) ∨ ((True ∨ False) ∧ True)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52750063327536529638811662542 : ((((p1 → ((p1 ∧ True) → ((p4 → (True → (p3 → p4))) ∨ False))) ∨ True) → (False ∧ (p2 → (p2 → (p4 ∨ (p2 ∨ (False ∨ p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149146370171969428444362127623 : (((True ∨ p5) ∧ (((p1 ∨ (False → (True → (p5 ∨ False)))) ∧ False) ∧ ((((False ∧ p1) ∨ False) ∧ p1) ∨ p5))) ∨ (((p5 ∨ p1) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327099281750618367440558465707 : (True → (((p3 ∨ p1) ∧ ((((p5 ∧ p3) ∨ ((p4 → p4) → (((True → ((p1 ∧ p2) ∨ p2)) ∨ p4) ∨ p3))) → (p1 ∨ p1)) ∧ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54113821732706392140791537720 : (((p4 ∧ (((True ∨ p1) ∨ ((p5 → p4) ∨ p5)) → True)) → ((((p4 ∨ True) ∧ (p3 ∧ p3)) ∨ (((p3 ∧ p1) → False) ∨ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319448094052704885126385300186 : (p4 ∨ ((((((((p3 ∧ p2) → p4) → p2) ∧ p4) ∧ p2) ∧ False) ∨ p2) ∨ (True → (p2 → (p4 → (p3 → (True ∨ ((p1 ∨ True) → True)))))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_688363548753567967451183399191 : ((((False ∧ (((False ∧ ((p2 ∧ False) → False)) ∨ ((p3 ∨ (True ∧ p3)) ∧ p1)) ∧ False)) ∧ (p2 → (True ∨ (((p4 ∧ p1) ∨ p1) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115420587944914073551548693124 : ((((p2 ∧ (p4 ∨ (False → (p1 ∨ p1)))) ∧ p1) ∨ ((p3 ∧ ((p1 ∧ p3) → (p3 ∧ (p3 → (p3 ∧ p1))))) ∨ (p3 ∨ p2))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62792738516652031950935662426 : ((p4 ∧ ((((False ∨ ((p4 ∧ (p1 → ((False → p2) → (p4 ∧ p5)))) → p1)) ∨ False) ∨ p5) ∨ ((True → (True ∧ (p4 ∨ True))) ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135436826853130964565120212703 : (((p2 → ((((((True ∧ (p3 → p1)) ∨ (p2 → p5)) ∧ p4) → False) ∨ p1) ∨ (True → True))) ∨ (p4 ∨ (p1 ∧ p2))) ∨ ((p1 ∧ p1) ∨ p3)) := by
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
theorem thm_5_vars_186123267628661795777618945088 : ((((True ∧ ((False → p1) ∨ p5)) ∨ ((False ∧ True) ∨ True)) ∨ p4) → ((((((p1 ∨ (False → True)) ∨ p2) → False) → (p5 ∧ p5)) ∨ p3) ∨ p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : ((p1 ∨ (False → True)) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h9
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h10 := h7 h8
        -- False on the left can always be used.
        apply False.elim h10
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h11 : ((p1 ∨ (False → True)) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h13 := h7 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h14
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h22 : ((p1 ∨ (False → True)) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h24 := h21 h22
        -- False on the left can always be used.
        apply False.elim h24
        -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
        have h25 : ((p1 ∨ (False → True)) ∨ p2) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h21, we can now drive its conclusion.
        let h27 := h21 h25
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h29
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h30 : ((p1 ∨ (False → True)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h31
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h32 := h29 h30
    -- False on the left can always be used.
    apply False.elim h32
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h33 : ((p1 ∨ (False → True)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h34
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h35 := h29 h33
    -- False on the left can always be used.
    apply False.elim h35



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310130269697459026271997731680 : (p2 ∨ (((p2 ∨ p1) → (((p4 → ((True ∨ p2) ∨ (False ∨ p1))) ∨ p5) → p4)) ∨ (p3 → ((True ∧ ((p5 ∨ p4) ∨ (p5 ∨ p4))) ∨ True)))) := by
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
theorem thm_5_vars_149982877677288182804321513035 : ((p4 ∨ ((p5 → p5) ∧ ((p3 ∧ (((False ∨ (True ∧ p2)) ∨ (p1 ∨ p3)) ∧ p5)) ∨ ((p4 → p5) ∨ False)))) ∨ (p3 ∨ ((p3 ∨ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4097105639284399372369444146 : (p3 ∨ ((p3 ∨ (((((p2 ∧ p1) → p1) ∧ (True → (p4 ∧ p1))) ∧ (p2 ∨ ((p2 → False) ∨ (p4 ∨ True)))) → p3)) ∨ (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37508341674809737129009068478 : (((((False ∨ p4) ∨ (((True ∧ ((p5 ∧ ((p4 ∧ p1) ∨ p5)) → True)) ∧ p1) ∨ ((p5 ∨ ((False → False) ∧ p2)) ∨ False))) ∨ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213710290816026336813365397800 : ((((p5 ∧ p5) → p2) ∨ p3) ∨ ((((((True ∧ (p2 ∧ False)) ∧ ((((p1 ∨ (p1 → p1)) ∧ p3) → p2) ∨ p1)) ∧ False) ∨ True) ∨ p2) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_684298875496661520223543427460 : (((((p3 ∨ (p2 → (((((False ∧ False) ∨ False) → False) → p1) ∧ False))) ∨ ((p3 ∧ True) ∨ p5)) ∨ ((p2 ∨ True) ∨ ((p5 ∨ p1) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114294114341160602282092534566 : ((((p2 ∧ (((p4 ∧ ((((p5 ∨ p5) ∨ p3) ∨ p2) → p3)) ∧ p4) ∨ False)) ∨ (True → True)) ∧ ((False ∧ (p5 ∨ p4)) ∧ p2)) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356390053922251782272269783221 : (p5 → (((False → p3) ∨ (((False ∧ (p2 → p2)) → ((p3 ∧ True) ∨ p2)) ∧ p1)) → (p4 → ((False ∨ ((p4 ∧ p2) ∨ (p3 ∨ p4))) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



