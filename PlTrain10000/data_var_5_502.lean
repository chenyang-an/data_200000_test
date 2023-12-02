variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255969007896201402028036785394 : ((True ∨ p3) → ((((p3 → False) ∧ (p5 ∧ (((p2 ∨ ((p5 ∧ (p1 ∧ (p1 ∨ False))) ∧ (p3 → p1))) ∨ (True ∨ p2)) → p2))) ∧ p1) ∨ True)) := by
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
theorem thm_5_vars_139626271155183421907518139223 : ((((p4 ∨ ((True → False) ∨ (p2 ∨ (True ∧ (p1 ∨ p1))))) → ((p3 → p4) ∨ (p3 → (p4 → (p1 ∨ p2))))) → p3) → (p3 ∧ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ ((True → False) ∨ (p2 ∨ (True ∧ (p1 ∨ p1))))) → ((p3 → p4) ∨ (p3 → (p4 → (p1 ∨ p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h9 := h7 h8
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Implications on the right can always be decomposed.
          intro h13
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h11
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h18
            -- Implications on the right can always be decomposed.
            intro h19
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
          case inr h20 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h21
            -- Implications on the right can always be decomposed.
            intro h22
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h23 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h23
  -- Implications on the right can always be decomposed.
  intro h24
  -- One of the premise coincides with the conclusion.
  exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301441469950005985800171127262 : (False ∨ ((p2 ∨ ((p1 ∧ p5) ∨ False)) → ((p1 ∨ (False ∨ (((p3 ∨ (p5 ∨ True)) ∨ p4) ∨ False))) ∨ ((((False ∧ p3) ∧ True) ∨ False) ∨ False)))) := by
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
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788034911800092802383914481546 : (((p5 ∨ ((((((True ∧ (p5 ∨ ((p1 ∨ ((p4 ∨ p3) ∧ (p5 ∧ p5))) → True))) → False) → (p5 ∧ (p4 ∧ False))) ∧ p3) ∨ p2) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307637559123804014600129821321 : (p1 ∨ (p1 → ((p4 → (p3 ∨ p4)) → ((p1 → p4) ∨ ((((False ∨ p1) ∨ (p1 → p3)) ∧ ((p5 → p1) ∨ (p2 ∧ (p4 ∨ False)))) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711593491316442765881075768046 : ((((p2 → (((False ∧ p5) ∨ True) ∨ False)) ∧ (p1 ∨ (((p2 → (p2 → p4)) ∨ p2) ∨ (((p5 ∨ p3) ∧ p4) ∨ (False → (p4 ∨ p2)))))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315831192084163935329527943269 : (p3 ∨ ((p5 ∨ p3) → (((((p1 ∧ (p5 ∧ p4)) → ((((p5 ∨ p3) ∧ (p2 ∧ p5)) ∨ (p4 ∧ p5)) ∨ False)) → (p2 ∨ False)) → p5) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299409458784437008138758273717 : (False ∨ ((p2 ∧ (p4 ∧ (((p4 → p2) ∨ (p3 → ((True → (((p1 ∨ p3) → p5) → (True ∧ False))) ∨ p4))) ∨ ((p4 ∧ p1) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342780409660773960273560558087 : (p2 → (((p3 ∨ (True ∨ ((p5 → p5) ∨ True))) ∨ p5) → ((p4 ∧ p2) ∨ ((p3 ∨ (p2 ∨ (p4 ∨ (p2 ∨ (True → True))))) ∧ (p2 ∨ p5))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343568113945405081367332176657 : (p2 → ((p5 ∨ p1) → (((p5 → ((((p2 ∧ (p1 ∧ True)) ∧ p4) ∨ p1) ∧ (p1 ∨ True))) ∨ (p3 ∨ p1)) ∨ ((True → p4) ∨ (False ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208582335824128099686081345040 : (((False → p4) → (False ∧ (False ∨ p5))) → ((((p1 → (p2 ∨ p5)) ∨ ((True ∨ (False ∨ ((p5 ∨ p3) → p2))) ∨ (p2 ∧ True))) ∨ p1) → False)) := by
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
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h5 : (False → p4) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- False on the left can always be used.
        apply False.elim h6
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h7 := h1 h5
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h12 : (False → p4) := by
            -- Implications on the right can always be decomposed.
            intro h13
            -- False on the left can always be used.
            apply False.elim h13
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h14 := h1 h12
          -- We need to get the left conjuct of h14 based on <expert-advice>.
          let h15 := h14.left
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- False on the left can always be used.
            apply False.elim h17
          case inr h18 =>
            -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
            have h19 : (False → p4) := by
              -- Implications on the right can always be decomposed.
              intro h20
              -- False on the left can always be used.
              apply False.elim h20
            -- We have shown the premise of h1, we can now drive its conclusion.
            let h21 := h1 h19
            -- We need to get the left conjuct of h21 based on <expert-advice>.
            let h22 := h21.left
            -- False on the left can always be used.
            apply False.elim h22
      case inr h23 =>
        -- Conjunctions on the left can always be decomposed.
        let h24 := h23.left
        let h25 := h23.right
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h26 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h27
          -- False on the left can always be used.
          apply False.elim h27
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h28 := h1 h26
        -- We need to get the left conjuct of h28 based on <expert-advice>.
        let h29 := h28.left
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h31 : (False → p4) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- False on the left can always be used.
      apply False.elim h32
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h33 := h1 h31
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766992049613015906120939221703 : (((p4 ∧ (p1 → ((p4 → ((p2 → (((((p3 ∨ p5) → False) ∨ (p5 ∨ p4)) → ((True → False) → p3)) ∨ (p5 ∧ p2))) ∧ p5)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38133435314491222976149056303 : (((((p4 ∨ p3) ∨ ((p3 ∧ (p4 → True)) → (((((True → p2) → p4) → p2) ∧ False) ∧ (p3 → True)))) ∧ (False → (p5 → p2))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51049865136911425941001349105 : (((p3 ∨ ((p1 ∧ ((p5 ∨ (p2 ∨ (True ∨ True))) → (p3 ∨ p5))) ∨ ((False → p1) ∧ False))) ∧ (p2 → (((p3 ∧ p3) ∨ p1) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152488232339175072267938257324 : ((((p2 ∨ p3) ∨ p4) ∨ ((p5 ∨ (p3 → ((((True ∨ p5) ∧ p2) → (False ∨ p4)) ∨ (p5 ∨ False)))) → p4)) → ((p5 → p1) ∨ (p1 ∨ True))) := by
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173806942673867241696851654038 : (((p4 ∧ (((False → ((p2 → ((p1 ∨ p1) → p2)) → True)) ∧ p2) ∨ p2)) ∨ p5) → (p1 ∨ ((True ∨ True) ∧ ((p3 ∨ True) ∨ (p4 → p4))))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774407659997859324322071039532 : (((False ∨ ((p3 ∨ (((p4 → (False ∧ (p5 → p3))) ∧ p5) ∧ ((p5 → p3) ∨ ((p2 → False) ∨ False)))) → ((p2 ∨ (p5 ∨ p3)) ∨ p1))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- False on the left can always be used.
        apply False.elim h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116472192781609724141613974009 : (((p1 ∧ True) ∧ (p1 ∧ (((p3 ∨ ((p5 ∨ (False ∨ ((True ∧ (p1 ∨ True)) ∨ (True ∨ p1)))) ∧ p4)) ∧ p1) ∧ (p1 ∨ p4)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38061932697945301979837306205 : ((((((((p1 ∨ p3) ∧ (p2 ∨ ((p1 ∧ p2) ∨ p1))) ∧ p3) ∨ p3) ∨ ((((True ∨ False) → p2) ∧ False) → p2)) → (p1 ∧ p5)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150349833816090828989919008187 : ((p5 → ((p2 ∨ ((p4 → (p2 ∨ (p3 ∨ p3))) ∧ True)) → (((p2 ∧ ((p4 ∧ p4) ∨ p3)) ∧ p1) ∧ p3))) ∨ ((p5 ∧ (False → p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48952534543692915058685059137 : ((((p1 ∨ (((((p5 ∧ p2) → ((p1 → p3) ∨ (p3 ∧ (p1 ∧ p5)))) ∧ p1) ∧ True) ∧ (p4 ∧ p4))) ∧ p2) ∨ (False ∧ (False → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221740118135992710501603266534 : (((False ∧ p5) → p2) ∧ ((((p5 → p3) → ((p1 → ((p1 → p2) → p1)) ∧ (p2 → p3))) → (p3 → False)) → ((p2 ∧ p3) ∨ (p3 → False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 → p3) → ((p1 → ((p1 → p2) → p1)) ∧ (p2 → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h8
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h6
  -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
  have h12 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h11, we can now drive its conclusion.
  let h13 := h11 h12
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808564074736908534158685215988 : (((p4 → (True → (((p1 ∧ ((True ∨ True) ∧ ((((p5 ∨ p3) ∧ p3) ∧ (p3 → p1)) ∨ ((p5 → p1) ∧ p1)))) ∧ (True ∧ False)) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110858756891379448851088809053 : ((((((p1 → (p4 ∧ (p3 ∧ (False ∨ (p4 ∧ (((p4 ∧ p5) ∧ ((True → p1) ∧ False)) → p1)))))) ∨ True) ∨ p3) → False) ∧ True) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113789013607178464838898764904 : ((((p2 ∨ p2) ∧ (p3 ∧ (((p3 → p1) ∧ ((p5 ∧ ((p1 → (p3 ∨ p3)) ∧ (p4 ∨ p3))) ∨ p1)) → p5))) → (p1 ∨ p3)) ∨ (p3 ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137667699985977179568992249909 : ((False ∨ (p3 ∨ ((p5 ∨ p3) ∧ ((True → ((((p4 ∧ p3) ∧ (p4 ∨ ((p5 ∨ False) ∨ True))) → p3) ∧ p4)) ∨ p5)))) ∨ ((False ∧ p2) → p2)) := by
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
theorem thm_5_vars_115306877093354861680077892519 : (((((False ∧ p4) → ((p2 ∨ False) ∧ p3)) ∧ (p2 ∧ p3)) → (p4 → (p5 → ((p5 → p2) → (((p4 → False) ∨ p2) ∨ False))))) ∨ (p3 ∧ p1)) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588690526024615449705037870333 : (((((p2 ∧ (((True → p1) ∧ ((p3 ∨ (((False ∧ p5) ∨ (p1 → True)) → p5)) ∧ p2)) ∨ (False ∨ ((p4 ∧ p4) → p4)))) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57851474536528505665234461080 : (((True ∨ (p2 ∨ p3)) → ((False ∨ ((((False ∨ (p4 ∧ p3)) ∨ (p5 → p5)) ∨ (p5 ∨ p5)) ∨ p5)) ∧ ((p2 ∨ p4) → (True ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256273364146717421022678545841 : ((False ∨ p1) → (((((p4 → (((((((p5 ∧ p2) ∨ ((p3 → p3) ∨ p2)) ∨ p5) ∧ p5) → False) → p1) ∨ p3)) ∧ True) ∧ p4) → p3) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41494861680673762901200461211 : (((((p1 → (((p1 ∨ False) → (p4 → p3)) ∧ (p1 ∨ p3))) → p1) → ((((p4 ∧ False) → p5) → (p2 → (True → p5))) → p4)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656902787927633830019240284810 : (((((((p4 ∨ p4) → p2) → p3) ∨ ((p1 ∧ ((p1 ∨ (((p1 → p3) → True) ∨ (p5 → (p1 ∧ True)))) ∨ p5)) ∨ True)) ∨ (p1 ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354151415508464309164501915926 : (p5 → ((((False ∨ (((p4 ∧ (p2 ∧ p3)) ∧ (p5 → p2)) ∧ (p3 ∧ False))) ∨ ((True ∨ (False → False)) ∧ (p5 ∧ (p5 → True)))) ∧ True) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203904063913281199485139413802 : ((p1 → (p1 ∨ ((p1 ∨ p1) ∧ p2))) ∧ (((((p4 ∧ (p5 ∨ ((p5 ∨ True) → p5))) → False) → (p3 → True)) → p3) ∨ ((True ∧ True) ∧ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340000989305563886586149471111 : (p1 → (p1 → ((p5 ∧ p3) ∨ ((p3 ∨ (p3 ∧ (((((((p4 → True) → (p2 → p4)) ∧ p5) → p4) ∨ (p3 ∨ False)) → True) → p3))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315629837641775207997866951776 : (p3 ∨ ((p4 → p4) ∧ (((p4 ∨ ((p4 ∨ (p3 → (p2 ∧ p4))) ∨ (p4 → (True ∧ False)))) ∧ p4) → ((p3 ∨ p5) ∨ ((p4 ∧ p3) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
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
    -- Implications on the right can always be decomposed.
    intro h6
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
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_130148598351760294200360216048 : (((((p5 → p1) ∧ True) ∨ (((p4 ∧ ((p3 ∧ True) ∨ p2)) ∨ (p1 → (p2 ∧ True))) ∨ (p4 ∨ p3))) ∨ (True ∨ False)) ∧ ((p5 ∧ p3) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51120390496845119893060941204 : ((((((p4 ∨ (p5 ∨ (False ∧ (p4 → (p5 ∧ p1))))) → p5) → ((True → False) ∨ p2)) ∨ p4) ∨ ((True ∨ ((p1 ∧ False) → False)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258181739260196871384998765714 : ((p4 ∨ p4) → ((p2 ∧ (((p3 ∨ p2) → (p5 ∨ False)) → p2)) ∨ (p5 ∨ ((((p1 ∨ (True ∧ p3)) → ((p1 → p1) ∧ p4)) ∨ p4) ∨ p2)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66423102707638920456065686204 : ((p5 ∨ (p4 → (((((True → (True ∨ p4)) → p5) → p3) → (False ∨ p5)) → (p4 → ((p3 ∧ (p3 ∧ (True ∧ (False ∧ p2)))) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167045737111088049891903659417 : (((((((False ∨ (p3 ∧ (True ∨ p5))) ∨ p4) ∨ ((p2 → p4) → p2)) ∧ p5) ∨ False) ∨ p4) → (p1 ∨ (p5 ∨ (p4 → ((p5 → True) ∨ p4))))) := by
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
      cases h4
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- False on the left can always be used.
            apply False.elim h8
          case inr h9 =>
            -- Conjunctions on the left can always be decomposed.
            let h10 := h9.left
            let h11 := h9.right
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h12 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h13 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h5
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h16 =>
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63033812515242868499637275580 : ((p5 ∧ (((p2 ∨ (p2 → ((p2 ∧ (p1 ∨ ((p4 → p1) → ((p4 → True) → p5)))) ∨ (p2 ∨ (True ∧ (p5 → p3)))))) ∧ False) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259285028423287364479231553566 : ((False → p1) → ((p3 ∧ True) → ((((p2 ∨ ((((p5 → False) ∧ p5) ∧ (p2 → (p1 ∧ p3))) → (p5 ∧ False))) → p1) ∨ (p3 ∧ False)) ∨ p3))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752406010169717226130837373715 : (((False ∧ (((p5 ∨ (p5 ∨ (((p1 ∧ (p4 ∧ ((((False ∧ p5) → False) → p3) → p4))) ∨ p1) ∧ p2))) ∨ (False ∨ (p1 ∨ p1))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909307779805922976108813464155 : ((((((True → p1) ∧ p2) ∧ ((((p5 ∧ p2) → (p1 → (p3 → (p5 ∧ p1)))) ∨ p4) → p5)) ∧ (((p5 ∧ p3) → (p2 ∨ p4)) ∨ p3)) → p1) ∧ True) := by
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
  cases h3
  case inl h8 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606621391715670361463202394408 : ((((((True ∨ (((((p2 ∨ p4) → ((((False ∨ ((p4 ∧ p5) → p3)) → p3) ∧ p2) → False)) ∧ p3) → p4) ∧ p5)) → p1) ∧ p4) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135452633147072454103037869468 : (((((p5 ∨ p5) ∨ (p5 → (p4 ∨ (p4 → (((p3 → (p2 ∧ p5)) → p1) → True))))) ∨ p1) → ((p3 → p4) → p5)) ∨ ((True → p4) → p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633999073119522660820848993492 : ((((((((p1 ∨ p4) ∨ (p1 → (((p2 ∧ (True → True)) → True) → p5))) ∧ ((p5 ∨ True) ∨ p2)) → (p1 → p1)) → (True ∧ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69227340353748579967804225407 : ((p5 → ((True ∨ ((p2 → True) ∧ True)) ∧ (p2 → ((p1 ∨ (p4 ∨ ((p2 → True) ∧ (False ∧ (p5 ∨ (p5 ∨ p3)))))) ∨ (True ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41235250602184767998026961936 : ((((p5 ∧ (((p1 ∧ ((p2 → p5) ∧ ((True ∨ p5) ∨ ((False ∧ p4) ∨ p2)))) ∧ True) ∧ p3)) ∧ (p1 ∨ (p3 ∨ (p1 → p2)))) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803591700003252557837411682221 : (((p3 → (((((p1 → p4) ∧ p5) ∨ (p5 ∨ p3)) → ((p1 ∨ p5) ∧ (p1 → (((p4 ∧ True) → True) → (p5 → (p4 ∨ p3)))))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659011325759998660354290135219 : ((((p1 → ((p5 ∨ (p2 → p5)) → ((((False ∧ ((p3 ∨ True) ∧ True)) ∨ p4) ∨ ((False ∨ True) ∧ p4)) ∨ (False ∧ p2)))) ∨ (p2 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301798563329072852532302345891 : (False ∨ ((p4 ∧ p2) ∨ ((p5 → ((p3 ∨ p2) ∧ p4)) → (((p2 ∨ False) ∨ ((p3 ∧ (False → p2)) → (p3 ∨ p1))) ∨ (p5 → (p1 ∨ False)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184275902104443055190903763676 : ((((p4 ∨ (((p4 ∨ p1) ∧ True) ∨ p3)) → (p2 → p4)) → False) ∨ (((p2 → p2) ∧ ((True → (p3 → False)) ∨ (True ∧ p3))) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165091028242851309630562306909 : (((p3 ∨ ((((p3 → p3) ∨ ((p1 ∨ p3) → ((p2 ∧ p3) ∨ True))) ∧ p3) → p1)) → p2) ∨ ((False ∨ ((False ∨ p5) → p5)) ∧ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53679013948420408415894890759 : (((True ∧ ((p3 ∨ p1) → (((p3 → True) ∨ p3) ∧ p5))) ∧ (p1 → (((p3 → ((p2 ∧ p2) ∨ False)) ∧ p4) ∧ (False ∧ (p4 ∧ p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229433509711719839627824740339 : ((p1 → (p1 → p3)) ∨ (((p3 ∧ p2) → False) → (p4 ∨ ((((False ∧ p1) ∨ (True ∧ True)) ∧ (p1 ∧ (((True → p5) → False) → p1))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50528869861091624063672897713 : ((((((p3 ∧ p5) ∨ (((p3 → (p3 → p3)) ∧ (True → False)) → (True ∨ (p4 → p2)))) ∧ p5) ∨ False) → (p4 ∨ ((True ∨ True) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261419417717939945214401133593 : ((p5 → p1) → (p1 ∨ (((p3 ∧ (p4 ∧ True)) ∧ (((p5 ∧ p4) ∧ (False → p5)) ∧ ((p1 ∨ p1) → True))) → (p1 ∨ (p2 ∧ (p2 → p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h15 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h15
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114344415109951026956473857525 : (((p4 ∨ ((((((p2 ∧ (p5 ∧ (p3 ∨ (p3 → True)))) ∨ p5) ∨ True) ∧ p2) ∧ True) ∨ False)) ∧ (False → ((p5 → True) ∨ False))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247713259811385571597080656578 : ((p1 ∨ False) ∨ (((p3 ∨ p4) ∨ ((p5 ∨ True) ∨ (False ∨ ((p2 ∨ p2) ∨ (p3 → ((p1 ∨ (p5 ∧ p1)) ∨ ((p5 ∨ p2) → p1))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51301839813607354800907926190 : (((False ∨ (p1 ∧ ((((p2 → (False → False)) ∧ (p4 ∨ p4)) ∨ (p2 → (p4 ∧ False))) ∧ p5))) ∨ (p5 ∧ ((p1 → (p4 ∧ p3)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303932971693480813294715806279 : (p1 ∨ (((((False ∨ False) ∧ (p2 ∨ (p3 → False))) → p3) → ((((p1 → (False → (p2 → p3))) ∧ True) → ((p4 ∧ p4) ∧ p1)) → p1)) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 → (False → (p2 → p3))) ∧ True) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213832742090269283920587485270 : (((p5 ∧ (False ∨ p4)) ∨ p4) ∨ ((True → (p3 ∨ False)) ∨ (((p5 ∧ (True ∨ p4)) ∧ ((p5 ∧ False) ∨ ((p5 ∨ True) → (p5 → p4)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137245670213157299043003149001 : ((p1 ∧ ((((True ∨ (p5 ∧ (True → (p4 ∧ False)))) ∧ p1) ∨ False) → (((True ∧ p2) ∨ p3) → ((p3 ∨ p1) → p5)))) ∨ (True ∨ (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157623315765554768697225787506 : (((((False → p5) ∧ ((True → p3) ∨ (p4 ∧ p3))) → (p4 → (p5 ∨ False))) ∧ (p2 → (p3 → p5))) ∨ ((p3 ∨ ((True ∨ p3) ∨ True)) ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53222887264500240417325469119 : (((((p3 ∨ p2) → (p4 ∨ False)) ∧ ((False ∨ True) ∨ (False ∧ p1))) ∨ ((((p2 ∧ p2) ∧ p4) → (True → p4)) ∨ ((p5 ∨ False) ∧ False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319379420128732579181147069650 : (p4 ∨ ((p5 ∧ ((((p4 ∧ (False ∧ False)) ∨ (p2 → p1)) ∧ (True → p5)) ∧ False)) ∨ ((p2 → (True ∨ p1)) ∨ ((False ∨ p5) ∧ (p1 ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305968514172650598704188230462 : (p1 ∨ ((True ∨ ((p3 → False) ∨ p2)) ∧ (True → ((((p3 ∨ ((True ∧ p5) ∧ p5)) ∧ p5) ∨ (False → (((p4 ∧ True) ∧ p5) → True))) ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54077123398206011499229835642 : ((((p5 ∧ p4) ∧ (((p4 ∧ True) ∨ True) ∨ (p2 ∨ False))) → (((p1 → p5) → False) → (((p2 ∨ p2) ∧ False) ∨ ((p3 ∨ p3) ∧ True)))) ∨ p3) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (p1 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h11
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : (p1 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h15
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : (p1 → p5) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h20
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636580632333371351047899484560 : (((((False ∨ (p1 ∨ (p3 ∨ (True → (p2 → ((True → (True ∨ p5)) → p3)))))) ∧ (((p1 ∧ (p5 ∨ p5)) ∨ (p5 → False)) → p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190099254268405061104395254958 : ((((p5 → ((p1 ∧ False) ∧ False)) ∨ (p3 ∨ False)) ∧ p4) ∨ (((p1 ∨ (p5 ∨ p5)) ∧ (True ∨ (p1 ∧ p3))) ∨ (((False ∨ p4) ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44846269992562850371117128557 : (((((p3 ∨ True) → True) ∨ ((p1 ∨ (p5 ∨ (((p5 ∧ (p2 ∨ (True → True))) → (((p4 ∧ p1) ∨ p1) ∨ p1)) ∧ True))) ∧ p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61555066009567813725526200822 : ((p1 ∧ ((((p3 → (p5 ∧ (False ∧ False))) → p1) ∧ p3) ∨ ((((p5 → False) ∨ (False → p4)) ∧ p4) ∨ (((p4 ∨ p4) ∧ p5) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139502105097420439800827499896 : ((((((p3 ∧ (p1 → p4)) ∨ ((p5 ∧ (p5 ∨ (p2 ∨ p1))) → p3)) → (p3 ∨ ((p3 ∨ True) → False))) → p2) → p2) → (p4 ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135097017056542927401428239082 : ((((((p4 ∧ (False ∧ False)) ∧ False) ∨ p5) ∧ (p5 ∨ ((((False → p4) ∧ p1) → True) ∨ (p3 ∨ p2)))) ∨ (True ∧ False)) ∨ (True ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164809003960314909728011146047 : ((((p1 ∧ p4) ∧ (False ∧ ((((False ∧ False) ∨ (False ∧ False)) ∧ p3) ∧ (p2 ∨ p5)))) ∨ p3) ∨ ((p5 → ((True → p1) → (p5 → True))) ∨ p1)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2272340408977299361934654869 : (((((False → (p5 → True)) ∧ ((p4 ∨ p2) ∧ (p2 ∨ p2))) ∧ p3) ∨ True) ∨ (p4 ∨ (p5 ∨ (True → (((p1 ∧ p3) → p5) → True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158204083965116956290900755701 : ((((p2 ∨ p3) ∨ p4) ∧ (p1 ∨ (p3 ∧ ((((p1 ∧ (p3 ∧ (p2 → False))) → False) ∨ False) ∧ p4)))) ∨ ((p2 ∧ (p4 ∧ (p1 ∧ p3))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787009152801076620078719180685 : (((p4 ∨ ((p1 → True) ∧ ((False ∧ (False ∧ ((p1 ∨ ((p4 ∨ ((p1 → True) ∨ p5)) ∧ p1)) → (p2 ∧ p4)))) ∨ ((False ∨ p2) → p2)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232263814087981688012901766661 : (((p2 → False) → p5) → (p3 → ((p3 ∧ (p2 ∧ (False ∧ (((p3 ∧ p3) → (False ∧ p5)) ∧ p2)))) ∨ (False ∨ (p2 → (p3 ∨ (False ∨ p4))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108063847384501284718822507961 : (((True ∨ False) → ((p3 ∧ ((p2 → ((True ∨ True) ∧ (((True ∧ p2) ∨ p5) ∧ p5))) → (True ∧ (p1 → p3)))) ∨ (True ∨ p5))) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- False on the left can always be used.
    apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58973281547634241381399356173 : (((p2 ∧ p4) ∨ (((((False ∨ p1) → p4) ∨ (p3 ∧ False)) → ((((True ∨ p2) ∨ p2) ∨ (p1 ∨ p4)) → (False ∨ (p4 ∨ True)))) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64969601269812435291117785682 : ((p2 ∨ ((((True → p1) ∨ (True ∧ p3)) ∧ p3) → (((p4 ∨ ((p5 → False) ∨ True)) → ((True → p4) ∧ ((p4 ∨ p3) ∧ True))) ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185522906128015044557644904473 : ((p3 ∨ (((p2 ∧ ((True ∨ p1) → (True ∧ False))) → p2) → p1)) ∨ ((p5 → ((False ∧ (p5 → (p2 ∧ ((p2 ∨ p2) ∧ p1)))) ∨ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158058301066888330126073510632 : (((p1 ∨ (p2 ∧ ((False ∨ p5) ∨ p5))) ∨ (p2 → (p1 → (False ∧ ((p5 ∧ (False → p1)) ∧ p4))))) ∨ ((False ∨ ((True ∧ False) ∨ True)) ∨ p1)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117755130320892607013308841451 : ((p4 ∧ ((p1 → (((p1 ∧ p5) ∨ p3) ∧ ((p3 ∧ ((((p1 ∨ False) ∨ p5) → ((p4 ∨ True) ∨ False)) ∨ False)) ∧ p2))) ∨ False)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111607965503566904646881657904 : ((((((((True ∧ False) ∨ p2) ∨ ((p5 ∧ (p3 → (False ∨ ((p5 → p4) → p2)))) → (False ∨ p2))) ∨ p1) ∨ p3) ∨ p4) ∨ p2) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172009062310715576733653620250 : (((((p2 ∨ ((False ∨ True) → (p4 → True))) ∧ p3) → (True ∧ p4)) ∨ (p1 ∨ True)) ∨ (True → (p2 ∨ ((p1 → p1) → ((True ∧ False) → True))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134035373423331756779297448278 : (((((((p2 ∧ False) ∧ (p4 ∨ (False ∧ (p1 ∨ p1)))) ∨ (p3 → p5)) ∨ ((p1 → p5) → (p3 ∧ False))) ∨ p5) ∨ True) ∨ (p3 ∨ (p3 → p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480860306525741880787569950416 : ((((((False → True) ∨ (p2 ∧ p5)) → (p2 ∨ False)) ∨ (p1 ∨ ((False → (((((p4 → p3) ∨ p5) → p5) ∧ False) ∧ p4)) ∨ (p3 ∨ p3)))) ∧ True) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123200114745299887354884643720 : ((((((True ∧ (p1 ∨ p3)) ∨ (((p3 → p4) ∧ (p2 ∨ p2)) → (p5 ∧ p2))) ∨ p5) ∨ p2) ∧ ((p5 ∧ p1) ∧ (p2 → p3))) → (p4 ∨ p5)) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h3.left
          let h11 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h10.left
          let h13 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h3.left
          let h16 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h3.left
        let h21 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h3.left
      let h26 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h27
  case inr h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h3.left
    let h31 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244606273441687044550444796602 : ((False ∧ p4) ∨ (p5 → ((p1 → (p2 → True)) ∧ ((p1 ∧ ((p5 → True) → ((((p5 → p1) → p3) ∧ True) ∨ p3))) ∨ ((p5 ∨ p1) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232741589523043615380055994138 : ((p1 ∧ (p1 → p5)) → (True ∧ (p1 ∧ ((p4 ∧ (p5 → p1)) ∨ (((((p5 → p4) ∨ (p4 → False)) → ((p5 → p2) → p4)) ∧ False) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682443508349234830424842273721 : ((((((p4 → ((False → p5) → (((p4 ∧ p4) ∧ False) ∧ False))) ∧ p3) ∨ ((False ∧ p4) → p4)) ∧ (((p4 ∧ p3) ∧ False) → (p5 ∧ p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the left can always be decomposed.
  let h9 := h4.left
  let h10 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341098785318711543027528067402 : (p2 → ((p3 → ((False → (((((True ∧ ((p2 ∨ p1) ∨ (((p5 ∨ True) → p5) → p3))) → p4) ∨ p2) ∧ p5) ∧ p3)) → (p5 → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613315151745738745290059324161 : ((((((p4 ∨ (p5 ∧ True)) ∨ ((((False → (p5 → p1)) ∧ p3) ∧ p3) ∧ (p5 → ((p3 ∨ (p3 ∨ p4)) ∨ p5)))) → (p2 ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_62397510545219422486476733863 : ((p3 ∧ ((((p3 → True) → p3) ∧ (((p5 → p5) → p4) ∨ p3)) ∨ (((((p4 ∨ p2) → False) ∧ (False ∨ p2)) ∨ p5) → (False ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67778913997182492562800679323 : ((p2 → ((False ∨ (((((p1 ∧ p1) → (p4 ∨ (p3 → (p1 → (True → p3))))) → (p3 ∧ p1)) ∨ p3) ∧ ((False → p3) ∨ p4))) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112572812919043391568578965814 : ((((p5 ∨ (((p5 → p1) ∨ p2) ∨ (((p1 ∧ True) → (p2 → ((False ∨ False) ∧ ((True ∨ p2) ∨ p3)))) ∨ True))) → True) → p3) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



