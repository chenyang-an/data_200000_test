variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64658742730162712880138256167 : ((p1 ∨ (False ∨ (((p1 ∧ ((p1 ∨ (((p4 ∧ False) ∧ p1) ∨ False)) ∧ p2)) ∧ (False → (p4 → ((p4 ∨ p5) ∧ (p3 ∨ p1))))) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191226696946322447775810783380 : (((p3 ∨ (False ∨ True)) → ((p2 ∨ False) ∨ (p2 → p3))) ∨ (((((p2 ∨ p3) ∧ False) ∧ ((p4 ∨ ((p1 ∧ False) ∧ p1)) → p4)) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253012408260117927625365225029 : ((True ∧ p3) → (((((True ∧ (((p5 → True) ∧ p3) ∧ p2)) ∧ (True → p4)) ∨ (p4 → p4)) → (False ∧ p2)) ∨ ((p3 ∧ True) → (True ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313010696067664397941506711854 : (p3 ∨ ((((p2 → ((True → (True → (False ∨ p5))) ∨ p3)) → (((((p1 ∧ p3) ∧ ((p3 ∧ p5) ∨ p3)) ∨ False) → p5) → p4)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19164777302452968851567758954 : ((((p3 ∧ p1) → (p2 ∨ (((((p5 → (True ∨ (p1 → p2))) ∨ p5) ∧ p4) → p4) → p4))) → (True → ((p3 → p4) ∨ (False → p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254773576709783633550500892393 : ((p3 ∧ p4) → (((p3 ∧ ((p2 ∨ (((p2 ∨ (p2 ∨ p3)) ∨ p1) ∨ p5)) ∨ (p5 ∨ p1))) → (False ∧ False)) ∨ ((p5 ∨ p4) ∨ (p4 ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172649941871583519233768402902 : (((p3 ∨ p2) ∧ (((p1 ∧ p1) ∧ ((p2 → p3) → False)) → ((p2 ∧ True) ∨ False))) ∨ (False ∨ ((p1 ∧ ((False ∧ p5) ∧ (p1 ∧ p3))) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778367874406958991178062275747 : (((p1 ∨ (p1 ∧ (p4 ∨ ((p4 ∨ (((p1 ∧ p4) → (p2 ∨ ((((False → p4) ∧ p1) ∧ p2) ∧ False))) → (p3 → p3))) ∧ (False ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216538439676874502395811199117 : ((p5 → (p5 → (False ∨ p4))) ∨ (p3 ∨ ((((False → (p1 ∧ p4)) ∧ (p2 ∨ (p2 → True))) ∧ ((p1 ∨ True) ∨ True)) → ((p3 ∨ True) ∨ p2)))) := by
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
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h15 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124640058710649163768555270530 : (((((p3 ∨ (False ∧ p4)) → p4) ∨ True) → ((False ∨ True) ∧ (((p1 → (p5 → ((p4 ∧ p3) ∨ p3))) → (p2 → False)) ∧ False))) → (p4 → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ (False ∧ p4)) → p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56453577978917086926219950333 : ((((False → p5) ∨ (p3 ∧ p1)) → (((p3 ∨ True) ∧ (p4 ∨ False)) → ((p5 ∧ (((p5 → p4) ∨ (p1 → True)) ∨ p1)) → (p2 ∨ p4)))) ∨ False) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h2.left
      let h9 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h12 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h13.left
            let h15 := h13.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h11
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h16
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h19 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
          case inr h20 =>
            -- Conjunctions on the left can always be decomposed.
            let h21 := h20.left
            let h22 := h20.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h18
        case inr h23 =>
          -- False on the left can always be used.
          apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h2.left
      let h26 := h2.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
          case inr h30 =>
            -- Conjunctions on the left can always be decomposed.
            let h31 := h30.left
            let h32 := h30.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
      case inr h34 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h36 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h35
          case inr h37 =>
            -- Conjunctions on the left can always be decomposed.
            let h38 := h37.left
            let h39 := h37.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h35
        case inr h40 =>
          -- False on the left can always be used.
          apply False.elim h40
  case inr h41 =>
    -- Conjunctions on the left can always be decomposed.
    let h42 := h2.left
    let h43 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h42
    case inl h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h45 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h46 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h45
        case inr h47 =>
          -- Conjunctions on the left can always be decomposed.
          let h48 := h47.left
          let h49 := h47.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h45
      case inr h50 =>
        -- False on the left can always be used.
        apply False.elim h50
    case inr h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h43
      case inl h52 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h53 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h52
        case inr h54 =>
          -- Conjunctions on the left can always be decomposed.
          let h55 := h54.left
          let h56 := h54.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h52
      case inr h57 =>
        -- False on the left can always be used.
        apply False.elim h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190694535301757827407949763981 : ((((p2 ∨ (p1 ∨ (False ∧ True))) ∧ p2) ∧ (p5 ∨ False)) ∨ ((((p3 ∧ (True → (p5 → p5))) ∨ ((p1 ∨ p4) ∨ (False → True))) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226779309238131890761537787064 : (((p2 ∧ p5) → p3) ∨ (((p5 ∧ (p2 → ((p4 ∧ p3) → p1))) ∨ p2) ∨ ((p5 ∧ (((p3 ∨ p3) → (p5 ∨ False)) ∧ (p1 → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792110576364824259636359926268 : (((True → ((((p3 → (p4 → True)) ∧ p2) → (((p1 → p5) ∧ p3) → (((p3 → p5) ∧ (p1 → False)) → False))) ∨ (p2 → (p2 → True)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227741006856969305721186916756 : ((p1 ∧ (p1 ∨ p3)) ∨ ((p4 ∧ p5) → ((((p2 ∧ p5) ∨ (p1 → ((((p1 ∧ (p5 ∧ True)) ∧ True) ∨ p2) ∧ (p1 ∧ p4)))) → p2) ∨ p4))) := by
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
theorem thm_5_vars_39554401703162354148877014829 : (((p1 ∨ ((((((False → False) → (True ∧ (p2 → (p4 → ((p5 → False) ∨ p4))))) → p2) ∧ p3) ∨ (p4 → (False ∨ p1))) ∨ True)) ∧ True) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167455756490459515928270859312 : (((True → (((False → p1) ∧ (p3 ∧ ((p1 → (True ∨ p3)) ∧ p2))) ∨ (p1 ∨ False))) → False) → (((p2 ∧ p5) ∧ ((p1 ∨ p3) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164857741360688589005276062982 : (((p1 ∨ ((p4 → (((True → ((p1 → p5) → p3)) ∧ (p3 ∨ p5)) ∧ p4)) → p2)) ∨ p3) ∨ (((p5 → p4) → True) ∧ ((p3 → True) ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227646023747408730649750545732 : ((False ∧ (p5 ∨ p4)) ∨ (((p5 ∧ (p3 ∧ p1)) ∨ ((((p5 → (p3 → True)) ∨ p2) ∨ p2) ∨ True)) → (((False → p4) → p2) ∨ (p2 → p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351206910072053673344973982170 : (p4 → ((((False ∨ (((p1 ∨ p1) ∨ (((p3 → p2) ∨ ((p3 ∧ p1) → False)) ∨ False)) ∧ (False ∨ p1))) → p3) ∧ p2) ∨ (True → (False ∨ True)))) := by
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
theorem thm_5_vars_326153883942338687182121717501 : (p5 ∨ (p2 → ((((p4 ∨ (((p1 ∧ p1) ∨ (p5 ∨ p2)) ∧ ((p4 ∧ False) → p1))) ∧ True) ∨ (((p3 ∨ p4) ∧ (p4 → False)) → p4)) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743311512010457395924726067365 : ((((p5 → False) ∨ ((p1 ∨ (p5 ∧ ((p5 ∧ (p3 ∧ False)) ∨ (p1 ∧ (((p2 → (True ∧ p2)) → p2) ∨ ((p4 ∨ p1) ∨ p2)))))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184176787251777133458748697679 : (((p2 → ((p1 ∧ (p4 → p4)) ∨ ((False ∧ p3) ∧ True))) ∨ p2) ∨ (p5 ∨ (True ∨ (((True → (False ∨ p2)) ∨ (False ∧ p2)) ∧ (p2 ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330360389804715123895753211108 : (True → (p2 ∨ ((p3 → (p2 ∧ (True → (((True ∧ p2) → (p3 ∨ p4)) → (False ∧ ((((p3 → (p2 ∨ True)) ∧ p5) → p5) → True)))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336135459396244463073593346167 : (p1 → (((p3 ∧ ((((False → ((False → p2) ∧ (((True → (True ∧ False)) ∨ p5) → (False ∨ p5)))) ∨ p1) → False) ∨ (p4 ∧ False))) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561579169910012603917988364 : (((p5 ∨ (p2 ∧ ((p4 ∨ p2) ∨ (((p5 ∧ p3) → (((False ∨ p1) → (p5 ∧ p3)) ∧ ((p3 ∨ p3) → False))) → p3)))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587472327398750688655006984283 : (((((((((((p2 ∧ p3) ∧ (p2 → p1)) ∧ (p2 ∧ p4)) → p2) ∨ (p2 ∨ p4)) → (p4 → (p5 ∧ (p5 ∧ True)))) ∨ p2) ∨ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57464844296429736349254465870 : (((True → (False ∨ p5)) ∨ (((p3 ∨ p3) ∨ p2) → ((p3 → (p2 ∧ p2)) ∧ (True → (True → (p3 ∨ ((p1 ∧ (p1 → p4)) → p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636843108300255656630104816703 : (((((((p1 → p1) → (False ∧ p2)) ∧ (p2 → ((p3 → True) ∧ (p5 → True)))) → ((p2 ∨ (p5 → ((True ∧ p3) ∧ True))) ∧ True)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39211808024669167715906695053 : (((True ∧ ((p5 ∨ ((p3 ∨ p4) ∧ ((((p5 → p4) ∧ p4) ∨ p4) ∧ (p4 ∨ (False ∨ p2))))) ∨ (p1 → ((p1 ∨ p5) ∨ p1)))) ∧ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219018901637174735525340227244 : ((p4 ∧ (p5 → (p2 → p4))) → ((((((p4 ∧ p1) ∨ p5) → p4) ∧ (p2 ∧ (True ∧ ((p5 → (p3 → p2)) ∨ (p4 ∧ False))))) ∧ True) ∨ p4)) := by
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
theorem thm_5_vars_693121377383113123437332964358 : ((((p3 ∧ (False → ((False ∨ True) ∨ (True ∨ (p3 ∨ (p2 → (p3 → p4))))))) ∧ ((p1 ∧ (False ∨ True)) ∨ ((p3 ∨ True) → (p3 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703969465981770439132541223707 : ((((((((p4 ∧ (p3 ∧ False)) ∧ False) ∧ True) ∨ p4) → p1) → ((p3 ∨ p3) ∧ ((p4 → True) ∧ ((True → (p5 ∧ p5)) ∨ (p4 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48228761121496245704242364124 : (((True ∧ ((True → p5) ∧ ((False ∧ True) ∨ (p4 → (((p5 ∨ p5) → p3) → (True ∨ (p2 → (p3 → (p1 → p4))))))))) → (p4 → p5)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80464166015276542162700729045 : (((((p3 ∨ (False ∧ p3)) ∨ p4) ∨ ((((False ∨ (p2 → p2)) → p3) ∨ (p1 ∨ (p5 → (p3 ∧ (p1 ∧ p4))))) → True)) → (p5 ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (False ∧ p3)) ∨ p4) ∨ ((((False ∨ (p2 → p2)) → p3) ∨ (p1 ∨ (p5 → (p3 ∧ (p1 ∧ p4))))) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185528990682957197807375698602 : ((p3 ∨ ((False → ((True ∧ p3) → p1)) ∧ ((p4 ∧ p3) ∧ p3))) ∨ ((True ∨ (p5 ∧ ((p3 ∨ ((p5 ∨ p2) → p4)) → p4))) → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309922563383183267000360218026 : (p2 ∨ ((((p1 ∨ ((p3 ∧ p1) ∧ p2)) ∨ (((p2 ∧ p2) ∨ p2) ∧ p2)) ∨ ((p2 → p4) → True)) ∨ (p5 ∧ (False ∨ ((p4 ∧ p5) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193754490323397433571226517573 : ((p3 ∧ (((p3 ∧ False) → p2) ∨ ((True ∨ p4) ∧ p4))) → (((((p4 ∧ (p2 → (True ∧ p1))) ∨ ((p5 ∧ p2) → p3)) → False) ∧ p5) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : ((p4 ∧ (p2 → (True ∧ p1))) ∨ ((p5 ∧ p2) → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h12 := h3 h8
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : ((p4 ∧ (p2 → (True ∧ p1))) ∨ ((p5 ∧ p2) → p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h17
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h23 : ((p4 ∧ (p2 → (True ∧ p1))) ∨ ((p5 ∧ p2) → p3)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h27 := h3 h23
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_931685493764982710636750290647 : ((((((((p1 ∧ p5) → p3) ∨ p2) → p5) ∧ p3) ∧ (p1 ∨ ((p3 → (p1 → p4)) → (False ∨ (((p4 → (True ∧ True)) ∨ False) ∨ p5))))) → p3) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218804772369372250340227326926 : ((p1 ∧ (p2 ∨ (p2 → p4))) → ((((p3 ∧ p4) → (((p2 ∧ p5) ∧ ((p5 ∨ (((True ∧ p3) ∧ p1) → p2)) ∨ p2)) ∨ p5)) ∨ p1) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47270879800018553081192298747 : ((((p1 ∧ ((p4 → p1) ∧ p2)) ∧ ((((p1 → p1) ∧ p5) ∧ ((p5 ∨ p2) → ((p4 → p5) → (p2 → True)))) ∨ p3)) ∨ (True → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348986258021539039684975121638 : (p3 → (p4 ∨ ((True → (True → (p2 ∨ (((p4 ∨ p1) ∧ (((p2 → ((True ∨ p5) ∧ p5)) ∧ p2) ∧ p2)) → p5)))) ∨ ((p5 → p4) ∧ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h6.left
    let h17 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h21 := h18 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- One of the premise coincides with the conclusion.
    exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117753983568911609934318316229 : ((p4 ∧ ((False ∨ (p2 ∨ ((((p3 ∧ (((p1 ∨ p3) → p4) ∨ p1)) → (p5 → True)) ∧ (True ∧ p5)) ∧ (p5 ∧ p5)))) ∨ p1)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41510253206121391346862086669 : ((((((p2 ∨ (p3 ∨ ((p1 ∨ False) ∨ p5))) → p1) ∧ p2) ∧ ((p3 → p4) → (((False ∧ False) ∧ p1) ∨ (False ∧ (False ∨ p4))))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172402409129271644305637882073 : (((p4 ∨ ((p2 ∨ p2) ∧ (p5 → p3))) → ((p5 ∧ (True ∧ (p2 → p5))) ∧ True)) ∨ ((p3 ∧ p5) ∨ (((p3 ∧ False) → False) ∨ (True → True)))) := by
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
theorem thm_5_vars_134635422789652641607967747160 : ((((p2 ∨ (p5 ∧ ((True → (p1 ∧ p1)) ∨ (((True ∧ False) ∧ p5) → p3)))) ∨ (p3 → ((p2 → p4) → p2))) → False) ∨ ((p2 ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116370047147549148482409908808 : ((((True ∨ p5) → p5) → (((p5 ∨ (((False → p2) ∨ False) → (p2 ∧ (p4 ∨ (p5 ∧ (p5 ∧ (p5 → p4))))))) ∨ True) ∨ True)) ∨ (False ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651856810698666213928857936688 : (((((p1 ∨ p1) → ((((False ∨ ((p5 ∧ p5) → (p2 ∨ (((False ∨ p1) ∧ p3) → (p2 ∨ p4))))) ∧ p2) ∨ p2) ∨ p2)) ∧ (p3 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231846853439193421192416944937 : (((p5 ∧ p3) → p4) → (True → ((((((True ∨ ((p3 ∨ p4) ∧ (True ∨ (p1 ∧ p5)))) → p5) ∨ True) → ((False ∧ p3) ∧ p1)) → p1) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∨ ((p3 ∨ p4) ∧ (True ∨ (p1 ∧ p5)))) → p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696659826283533121456493110925 : (((((p4 ∧ (True → ((p4 → (p2 ∨ (False → p1))) ∧ p1))) ∨ p1) ∧ ((p3 → True) → (((False ∨ (p4 ∨ (p5 → p4))) → p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172179778234891814173937956943 : (((p4 ∧ ((p4 ∨ (p4 → (p1 ∨ p2))) ∨ (p5 ∧ False))) ∨ ((False → False) ∨ False)) ∨ (((((p3 → (p1 ∧ p3)) ∨ p2) ∧ True) → p2) ∨ p3)) := by
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
theorem thm_5_vars_216916832332115008823373462210 : (((p5 ∨ (p4 ∧ False)) ∧ p4) → ((p3 ∨ (((p5 ∧ (p4 ∨ p4)) ∧ p1) → ((p3 → (((p5 ∧ p2) ∨ False) ∨ True)) ∨ p1))) ∨ (p2 → True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305723925058064609818634219468 : (p1 ∨ ((p4 → (False ∨ ((p5 ∧ p2) ∨ ((p4 → p2) → p5)))) → (((((False ∧ False) ∨ True) ∨ p4) → p4) ∨ (False → (p2 → (p5 ∨ True)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32153659033739475333820324158 : ((p1 ∨ ((p1 ∨ (((((p3 ∨ p1) ∧ (p3 → p3)) → False) ∧ p1) ∨ True)) ∨ (((p2 ∨ p2) ∨ (p4 ∨ (False → p3))) → (p3 ∧ False)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_54281485603188453879368674547 : (((((True ∨ p4) ∧ False) → ((p3 ∧ p4) → p5)) ∧ ((((p4 ∨ p1) → ((p3 ∨ p4) ∧ (p3 → (p4 ∧ p2)))) ∧ (False ∧ p2)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594447684759741060308722277784 : ((((((((True → p3) ∧ True) ∨ ((True ∨ p5) ∧ (((p5 ∨ p3) ∨ False) ∧ p2))) ∧ True) ∨ (p4 → ((p5 → p1) → (p3 ∧ True)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192562718666729077288747400240 : (((p2 ∨ (((p3 ∨ (p2 → p2)) ∧ False) ∧ p2)) ∨ p5) → (((p2 → ((p4 ∨ p5) ∧ p3)) ∧ (False ∨ (p2 → ((p2 → p4) ∨ p5)))) ∨ True)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h5.left
      let h8 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h8
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157218552822309770366502833696 : (((((p1 → (p3 → ((False → p1) → ((p2 → False) ∨ p1)))) → p3) ∨ (p5 → (False ∧ False))) → p3) ∨ (((False ∨ p4) → p2) ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65569363050918114724826809543 : ((p3 ∨ (p3 → (p4 ∨ ((((p5 ∨ p1) ∧ (p4 ∧ ((False → p3) ∨ ((((p5 → p4) → False) ∨ (p3 → p5)) → p1)))) → p5) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147643126891338349338319710370 : ((((False ∨ (p1 ∧ ((p1 ∧ ((p4 ∨ True) ∨ ((False → p2) ∨ ((p1 ∨ p2) ∨ True)))) ∧ p2))) → True) → False) ∨ ((p3 ∧ p4) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165616750776604759956903260523 : (((p3 → (((False → p3) → (p3 → p3)) → p1)) → ((p4 → (p1 ∨ p1)) ∧ (p4 ∧ True))) ∨ (False → (((p3 → p4) ∨ (p2 ∨ p4)) → p1))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157505828530847940321050035755 : (((True ∧ (((p2 → (((False ∨ p3) ∨ False) → (p1 ∧ p1))) ∨ (p5 ∧ p2)) → p1)) ∨ (p4 → p5)) ∨ (((True → (p3 ∨ False)) ∨ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340821369791741159896363206605 : (p2 → ((((((((False → p2) ∨ p1) → p1) ∨ (((p2 ∨ (p1 ∧ (True ∨ p4))) ∨ p1) ∨ p5)) ∧ p4) → (p5 ∧ p1)) ∨ (p2 ∨ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137832526621197718228604683260 : ((p3 ∨ ((((p2 → (p5 ∨ (True ∨ ((p5 ∧ (True ∨ (p4 ∧ p3))) → p5)))) ∨ False) → p5) ∧ (p2 → (p2 ∨ p2)))) ∨ ((True ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137003296765752767183975179780 : (((False ∨ p2) → (False ∨ ((((True → p4) → False) → False) → (((p5 ∧ p1) ∨ False) ∧ (p3 ∨ (p5 ∨ (p5 → True))))))) ∨ ((False ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354703585108163432479476268116 : (p5 → ((((p1 ∧ ((p4 → True) ∧ (p2 ∨ (p1 → p5)))) → (((p5 ∧ True) → p3) ∨ (((p2 → p2) ∨ p4) → p2))) → (False ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738822228683998958160597862094 : ((((p2 ∧ p5) ∨ (((((p5 ∧ (p1 ∨ (p4 ∨ p4))) ∨ (True ∧ p4)) ∨ (p1 ∧ (p4 ∧ (p1 ∨ (p4 → True))))) ∧ (p1 → p5)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49737152638151192622908329102 : (((p3 ∧ ((((False → p5) → (((((True ∨ False) ∨ p5) → p2) ∧ (p4 → p5)) ∨ p2)) ∨ (True → p3)) → True)) → ((True ∧ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664239895410692396262094684658 : ((((p1 ∨ ((p2 ∧ (((((p5 ∧ True) ∧ p1) ∧ p5) ∨ (p2 ∨ ((p1 ∧ True) ∨ True))) ∧ True)) → ((p3 → p4) → True))) → (p4 → p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682805313475726887969490378852 : (((((p4 → (p4 → p4)) ∧ (((p5 ∨ p5) ∨ (p3 → p2)) → ((p5 ∧ (p1 → p5)) ∧ p5))) ∧ ((False ∨ False) → ((p3 ∧ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198265071360108049758222351128 : ((False ∧ ((p1 → ((True ∧ p1) → False)) → p4)) ∨ (((True ∧ p5) ∧ ((p3 ∨ (p2 ∨ p5)) ∧ (p4 → (True ∧ (False → (p5 ∨ True)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315482876049547232920031632881 : (p3 ∨ (((False → p5) → p1) → ((p1 → (p2 ∧ (False ∧ ((False ∨ p2) ∧ ((p5 ∧ ((p1 → p1) ∨ ((p1 ∧ p4) → p1))) → p5))))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62303081576801636481111291125 : ((p3 ∧ ((((p2 ∧ ((True ∧ False) → (p2 ∨ (p1 → True)))) → (False → (False → p5))) ∧ (p4 ∨ ((p2 ∧ p3) ∧ p2))) ∧ (True ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238281611585521073199890152221 : ((True ∨ p5) ∧ (p1 ∨ ((True → p5) ∨ ((((p4 ∨ ((p5 → False) → (True ∧ False))) ∧ p5) ∨ True) ∨ (p1 ∨ ((p2 ∨ (p1 ∨ p1)) ∧ True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_342246681720190166976586488725 : (p2 → (((p3 ∧ (p3 ∨ ((p1 ∧ (p2 ∨ (False ∧ True))) ∨ (False ∨ p1)))) ∨ (p5 ∨ (False → p1))) ∧ (((True ∧ True) ∧ False) → (p3 → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777183924946909504950708297116 : (((p1 ∨ (((p4 → (p5 ∧ (p2 → ((p2 → (True ∨ p3)) → p1)))) ∨ (p5 ∧ ((p3 → (p4 ∧ False)) ∧ p1))) ∧ (p5 ∧ (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56592918146456065020979357216 : (((p3 → ((False ∧ p5) ∧ p5)) → ((p1 → p4) → ((p3 ∧ True) ∨ (((p5 ∧ p1) ∨ (((p2 → p2) ∨ p4) ∨ p5)) ∨ (False ∧ p5))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60291947217875517626737657633 : (((p1 → False) → (((p1 → p3) ∨ (p5 → (p1 ∨ p5))) → (((p5 ∧ p4) ∧ ((p5 → (p3 ∧ ((p5 → p5) → False))) ∨ p3)) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710121164007096947055095807417 : ((((((p1 ∨ (p4 → p4)) ∧ True) ∨ p1) ∧ (p5 ∧ ((((p4 ∨ p3) ∧ ((False ∧ p5) → (p2 ∨ p3))) ∨ p4) ∨ ((p4 ∧ p4) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345441296357003087635854289907 : (p3 → (((((p2 ∨ (p2 ∨ (True ∨ True))) → ((p2 ∨ (((False ∧ p1) ∧ True) ∨ (p2 → (p3 ∨ p1)))) ∨ p3)) ∧ p2) ∨ (False → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187511103425518980261831034242 : ((p1 ∨ (((p4 ∧ ((False → p4) ∨ p1)) → (p3 ∧ p5)) → p1)) → (p5 → (p5 ∧ ((((False ∨ p5) → p5) → False) → (p3 ∨ (p3 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : ((False ∨ p5) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h7
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : ((False ∨ p5) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h13
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322449697111007907500657741850 : (p5 ∨ ((((p2 ∨ p4) → (p1 → p3)) → (((p3 → (True ∧ ((True ∨ ((p3 ∨ False) ∧ p2)) ∧ p3))) → False) → (p4 ∧ (p3 ∨ p5)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56464370334407572886601551524 : ((((p4 ∧ False) → (p5 → p1)) → (p4 ∨ ((p2 → False) ∨ (True ∧ (((p2 → p5) → (True ∧ (False → (p3 ∨ (p2 → p2))))) ∨ p2))))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342386091027130167399378588445 : (p2 → (((((p5 ∨ False) ∧ ((p2 → p3) ∨ False)) ∧ (True → (p4 → True))) ∧ (p1 ∧ True)) ∨ (p1 ∨ ((p1 → p5) ∨ ((p2 ∧ p2) ∨ True))))) := by
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
theorem thm_5_vars_118425832753555845787480800866 : ((p2 ∨ (p2 ∨ (((p4 ∧ (True ∧ p2)) ∨ p1) ∨ ((True ∨ ((p2 → False) ∨ p4)) ∨ (p4 ∨ (((p4 → p5) ∨ p4) ∨ p1)))))) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655105759123064581724620646110 : (((((p2 ∨ ((((p5 → ((p4 ∧ p2) ∧ p3)) → p1) ∧ p5) ∨ ((p2 ∨ True) → (False → ((p5 ∧ True) ∨ p1))))) → p4) ∨ (p2 ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_135897245160224550603909800578 : ((((((True ∨ (p5 → (False → p5))) ∨ p5) → (p3 → p2)) ∨ p3) → (((p1 → False) ∨ (p3 ∨ (p3 → p1))) ∧ True)) ∨ (True ∧ (True ∨ p1))) := by
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
theorem thm_5_vars_646448468062300339483128892517 : ((((p1 → ((p2 → (p3 ∨ (p1 ∨ (((((((p2 ∧ p1) → p3) → p4) ∧ p5) ∨ (True ∧ (True ∧ p4))) → True) ∨ p2)))) ∨ p4)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135744894061340827159806398287 : (((((p1 ∨ p2) → (p1 ∧ p1)) ∧ (False ∨ ((p1 → p4) ∧ (False → p4)))) ∨ (((p3 ∨ (p2 ∨ p4)) → p3) → False)) ∨ (True ∨ (False ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342595908594726685243021696607 : (p2 → ((((((False ∨ ((False ∨ p1) ∧ p4)) ∨ p4) ∧ p4) ∨ p2) → p5) → (((((p3 → (p2 ∨ p5)) ∧ (p3 → p1)) → p5) ∧ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134569774501424783669273631056 : ((((((p3 ∨ False) ∨ ((p2 ∨ (False ∧ p1)) → (p2 ∨ ((p4 → (p5 → p1)) ∧ p3)))) → True) ∧ (p2 → p5)) → False) ∨ ((p3 ∧ False) → p4)) := by
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
theorem thm_5_vars_219846389716754750540480236515 : ((p3 → (True ∧ (False ∨ p3))) → (((p1 → True) ∧ (p2 ∨ ((p1 → (((p1 ∧ (p4 → (p1 ∧ p2))) ∧ (p1 ∨ p4)) ∨ p3)) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199339507547374543481955612052 : (((((True → True) ∨ (p1 ∨ p5)) → p3) ∨ p3) → (((((p3 → p1) ∧ True) ∧ p2) → (False ∨ (((True → p1) ∨ (p2 → p4)) → p3))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((True → True) ∨ (p1 ∨ p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137435022946035222585006127529 : ((p4 ∧ ((True ∧ (((((p1 ∨ (p4 ∧ p3)) ∧ p2) → (((False → p1) → p4) → p1)) → p4) ∧ p5)) → (p3 → p2))) ∨ (p5 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116749012613229412305957880386 : (((p5 ∧ False) ∨ ((True → (p5 ∧ (p5 → p4))) ∧ (p5 ∧ ((((p5 ∨ (p2 ∨ False)) ∧ p3) → p1) ∧ (p5 ∧ (p2 ∧ True)))))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198395522767420731305568614916 : ((p3 ∧ (p3 ∨ ((True ∧ p1) ∧ (False ∨ p4)))) ∨ ((p2 ∨ ((p5 ∧ ((p2 ∨ (p1 → p5)) ∨ (p3 → p3))) ∧ (False ∨ p3))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227605532175054021719212300623 : ((False ∧ (p5 ∧ p3)) ∨ (((p1 → ((p2 → p3) ∧ p3)) ∨ ((True ∧ (p3 → (False → (p5 → ((p1 ∨ False) ∨ True))))) ∧ (True ∨ False))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217548568996745572350747049893 : ((((False ∧ p3) ∨ p5) → p4) → ((((False ∧ (p4 ∨ p5)) ∧ p3) ∧ (((p1 ∨ p5) → (True ∨ p2)) ∨ (p5 → ((p2 ∧ p2) ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148682160475119534289583679899 : ((((p5 ∧ (p1 → False)) ∧ (False ∧ (True ∨ False))) ∨ (((p3 → p1) ∨ (p3 ∨ p4)) ∧ ((p1 ∧ p4) ∨ False))) ∨ (p5 ∨ (p3 ∨ (p4 → True)))) := by
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
theorem thm_5_vars_139874071172080698982022001995 : (((((True ∨ ((((p5 → ((p4 ∨ p1) → p5)) → ((True ∧ p3) ∨ p1)) ∨ p1) ∧ p4)) → False) ∨ False) ∧ (p3 → p4)) → (False ∧ (p2 ∧ p3))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ ((((p5 → ((p4 ∨ p1) → p5)) → ((True ∧ p3) ∨ p1)) ∨ p1) ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (True ∨ ((((p5 → ((p4 ∨ p1) → p5)) → ((True ∧ p3) ∨ p1)) ∨ p1) ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13
  -- Conjunctions on the left can always be decomposed.
  let h14 := h1.left
  let h15 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h16 =>
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h17 : (True ∨ ((((p5 → ((p4 ∨ p1) → p5)) → ((True ∧ p3) ∨ p1)) ∨ p1) ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h18 := h16 h17
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19



