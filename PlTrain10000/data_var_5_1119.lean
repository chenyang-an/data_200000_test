variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219070938525202442336465467883 : ((p5 ∧ (p3 ∨ (p3 → p4))) → ((p5 → ((p4 ∨ p3) → ((p2 → (p4 → False)) → p3))) → ((((True ∨ p4) ∨ (False → p1)) → p4) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226499849227417957440573002154 : (((p2 → p4) ∨ p5) ∨ (((True → p4) → p5) → ((p1 → False) → ((True → (p1 → (((p5 ∨ p3) → (True ∧ False)) ∨ p5))) ∨ (False ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60977207433583740813304317926 : ((False ∧ ((False ∨ (((p5 ∨ (((False → (True ∨ p1)) → True) → ((p5 ∧ p5) ∧ True))) ∨ (True → p3)) → ((p4 ∨ p5) ∧ False))) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39768981723136422513340517318 : (((True → (((p1 → False) → (True ∧ p2)) ∨ (True → ((((True ∨ p3) ∧ (p1 → p5)) ∧ ((False ∧ p4) ∨ (p1 ∨ False))) ∨ p4)))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134996642184955624317302816765 : (((p1 ∧ ((p1 ∧ ((p2 ∨ p5) → False)) ∨ ((p4 ∧ False) → (((p1 → (p2 ∨ p1)) ∨ p3) ∨ p2)))) ∧ (p2 → False)) ∨ (p3 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690071209905842077982068826601 : ((((p5 ∧ ((((((p2 → p2) → p2) → p5) ∨ p3) ∨ (p4 → p2)) ∧ (p3 ∧ False))) ∨ ((p5 ∧ (p3 ∨ (p5 → (False ∧ p2)))) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936907187188980341655369967429 : (((((((False ∨ p2) ∧ False) → p2) → p1) ∧ ((p5 → p4) ∨ (((((True → p3) → p3) ∨ p3) ∧ ((True → (p4 ∧ p1)) → p4)) ∨ False))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (((False ∨ p2) ∧ False) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
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
        apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h17 : (((False ∨ p2) ∧ False) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h18
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- False on the left can always be used.
            apply False.elim h20
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h17
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h25 : (((False ∨ p2) ∧ False) → p2) := by
          -- Implications on the right can always be decomposed.
          intro h26
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h29 =>
            -- False on the left can always be used.
            apply False.elim h29
          case inr h30 =>
            -- False on the left can always be used.
            apply False.elim h28
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h31 := h2 h25
        -- One of the premise coincides with the conclusion.
        exact h31
    case inr h32 =>
      -- False on the left can always be used.
      apply False.elim h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618074363139955049361853582476 : ((((((p3 ∧ p3) ∨ (p4 → p4)) ∧ ((False ∧ p2) ∨ ((p3 → (p2 ∨ ((p5 → p2) ∨ ((False → True) ∧ (p4 ∨ p3))))) → p5))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355650219844883703192389180313 : (p5 → (((((p2 ∨ (p4 ∧ p4)) ∨ True) ∧ (((True → (p3 ∨ (p3 ∨ p5))) → p4) ∨ (p2 ∧ (p3 → (p2 ∨ True))))) ∧ p1) → (p3 ∨ p5))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124197542111615891586737877801 : (((p4 ∧ (((p1 ∧ p2) ∨ ((p4 → p5) ∧ p1)) ∧ p2)) ∨ ((p4 ∧ (False ∨ (p2 ∨ p4))) ∨ ((True ∨ p5) → (p4 ∧ p5)))) → (False ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
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
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60416587280702319303792830325 : (((p4 → p1) → (True ∧ (((((p3 ∧ (True ∨ ((True ∨ (p2 → p5)) ∨ False))) → p4) ∨ (p4 → p4)) ∧ p2) ∧ ((p3 ∧ p1) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167936210434439589152988559590 : (((True ∧ ((p2 → (p3 ∨ p1)) ∨ (p1 → p3))) ∨ ((((p2 ∧ p4) → p3) ∨ False) ∧ p5)) → ((p4 ∨ ((p5 ∨ False) ∨ (p5 ∨ True))) ∨ False)) := by
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
    case inr h6 =>
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
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308369727869559764287129938066 : (p2 ∨ ((((p2 ∨ ((((p4 → p2) → p1) → p4) ∧ (((((False → (p4 ∧ True)) → False) → True) → p3) ∧ (p3 → False)))) ∧ p5) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324248491074033086103449473377 : (p5 ∨ ((p4 → (False ∨ ((p1 ∨ (p4 ∨ p2)) → True))) ∧ ((p2 ∧ ((True → False) ∨ p5)) ∨ (True ∨ (False ∧ ((p1 → p4) ∧ (p3 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341049611660945149207305982978 : (p2 → ((p1 ∨ (((p3 ∨ False) ∧ p3) ∨ (p2 → (((p3 ∨ p4) ∧ True) ∨ (((False ∨ True) → (((p2 → p1) ∨ p1) ∨ p2)) → p5))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257460971937107186534302239677 : ((p3 ∨ True) → ((p2 → True) ∧ (p5 ∨ ((p5 → False) ∨ (p2 → (p4 ∨ (True ∨ (p3 → (((p3 ∧ (p2 ∨ (p3 ∧ p3))) ∨ p1) ∧ p5))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197954549278204142517515109599 : (((p3 ∧ p2) ∧ (p2 ∧ (p4 ∨ (p2 ∨ p2)))) ∨ (p5 ∨ ((p1 → (True ∨ ((False ∧ (p3 → False)) → True))) → (p1 → (p2 → (p1 ∧ p1)))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218560186806196675010625411355 : (((False → p1) → (p2 ∨ p2)) → ((p5 ∨ (((p3 ∧ ((True ∧ p1) ∧ p1)) ∨ ((p3 → p5) ∧ (p4 ∧ p2))) ∧ p2)) ∨ ((True ∨ True) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164702518554414452323265691662 : (((((p1 ∧ (False ∨ False)) ∧ (((p3 → p1) → (p4 ∨ (True ∧ p2))) ∨ p1)) ∨ p5) ∨ False) ∨ (p2 → ((p5 → (p1 → p3)) → (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156864715608758352405678553785 : ((((((p5 ∨ False) ∨ ((p4 → (p1 ∧ p2)) ∨ p5)) ∨ ((p3 ∧ (p2 ∧ p1)) → False)) ∧ p4) ∨ True) ∨ ((((True ∧ p1) ∧ p4) ∨ p3) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44446395766024060161147700297 : (((((((p3 → p3) ∧ (True → p4)) ∧ (p5 → (True ∨ p2))) ∨ True) ∨ ((p4 ∧ (p2 → (p5 → (p5 ∧ p1)))) ∨ (True ∨ p5))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41921243446229387788342563510 : ((((p2 ∧ (p3 ∨ True)) → (((((p2 ∧ (p1 → p4)) ∨ (p3 → False)) → p5) ∧ (p5 ∧ True)) → (((p2 ∨ p1) ∧ True) ∧ p3))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777413626843472381014160457815 : (((p1 ∨ ((((False ∨ (((p2 ∧ True) ∨ ((p4 → True) ∨ True)) ∧ p2)) ∨ (p4 ∧ p5)) ∧ True) ∨ (((p5 ∨ p5) → (True ∨ False)) ∨ p3))) ∨ p3) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64976465164856966037132405233 : ((p2 ∨ ((p1 ∨ (False ∧ (p1 ∧ p5))) ∧ ((p3 ∧ (((p3 → p3) → (p1 ∨ ((True → False) ∧ (p1 → (p4 ∧ p1))))) → p4)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309649359650907951081540846614 : (p2 ∨ ((p3 ∧ (((p5 ∨ p1) ∨ p3) → ((True ∧ p5) ∨ ((((p1 → True) ∨ p2) ∧ p5) → (p2 ∨ (True ∧ True)))))) ∨ ((p5 ∧ p3) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_51003759435486346981749130797 : ((((True ∨ True) → ((((p4 ∨ p3) ∧ (False → (False ∧ p1))) ∨ ((p5 ∨ True) ∧ p1)) ∨ p2)) ∧ ((p2 → p5) ∨ ((p5 ∨ p3) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65375911774935516426051950868 : ((p3 ∨ (((((p1 → (p1 ∨ p2)) ∨ p2) ∨ p5) → (True → p2)) → ((p2 ∧ (p4 ∨ p2)) ∧ (True ∨ (p3 ∨ (True ∨ (p3 ∨ p1))))))) ∨ p3) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → (p1 ∨ p2)) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (((p1 → (p1 ∨ p2)) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h11
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2817539221547098433327672950 : ((((True ∨ p1) ∨ p3) ∨ p2) → (((False ∨ ((False → True) → p2)) ∨ p1) → (p4 ∨ ((p1 ∧ p3) ∨ (False ∨ (False ∨ (False → p2))))))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h8 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h9
            -- False on the left can always be used.
            apply False.elim h9
          case inr h10 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h11
            -- False on the left can always be used.
            apply False.elim h11
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- False on the left can always be used.
          apply False.elim h22
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h16
        -- One of the premise coincides with the conclusion.
        exact h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157112761452933600443254115535 : (((p5 → ((p4 → ((p2 ∨ p3) ∧ ((p2 ∨ p3) ∨ p2))) ∧ ((p4 ∨ True) ∧ (p2 ∨ p5)))) ∨ p5) ∨ (False → ((p5 ∨ (False ∧ p3)) → p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249973615816658433333073114751 : ((True → p2) ∨ ((((p5 → ((p1 → ((p5 ∧ p2) → True)) → (p3 → False))) → (p5 ∨ p2)) ∧ (True → (True → False))) ∨ (p1 ∨ (True ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135446982702584073741849535916 : ((((p4 ∨ ((p4 → p5) ∨ (((p1 ∨ p1) ∨ (False ∧ True)) ∧ (True ∨ (p3 ∧ p1))))) ∧ p3) → (p4 ∨ (p3 → p1))) ∨ (True ∨ (True → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59030406574285515034903552273 : (((p4 ∧ False) ∨ ((((True ∧ True) → ((((p2 → (((p4 ∧ p5) ∧ (p4 → p2)) ∨ False)) → (False ∨ p1)) ∨ p1) ∧ p2)) → False) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147113756401567937111033047620 : ((((True → p4) ∧ ((((((p5 ∨ p1) ∨ False) ∧ True) ∧ (p4 ∧ False)) ∧ p3) ∧ (True → (p5 ∨ p3)))) ∧ False) ∨ ((p2 ∨ (False → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_10500489130314420140483391259 : (((p2 → (((False ∨ ((p1 ∧ False) → p3)) ∧ p2) → ((((p3 ∧ (p1 ∧ (p4 → (False ∨ p2)))) ∧ (p4 → p5)) ∨ p1) ∨ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134360719314432724625237438328 : (((False ∨ (p2 → ((False ∨ p3) ∨ (True ∧ ((((((p4 → p1) ∧ p1) → p5) → (p1 ∨ p1)) → p1) → p3))))) ∨ p3) ∨ ((False ∨ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51139064026248755533507602273 : ((((((True ∧ p3) → ((((p3 → p1) → p5) ∧ (p2 ∧ (p2 → True))) → p5)) ∨ p2) → p2) ∨ (False → (((p2 ∧ p3) ∧ p3) ∧ True))) ∨ p5) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83404480948688517176587421955 : (((p1 ∨ ((((p4 ∧ p3) → p4) ∨ p5) → ((p4 → p1) ∧ (((True → p5) → p1) ∧ False)))) ∧ (((p1 ∧ True) → (True → p5)) ∧ p3)) → p1) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (((p4 ∧ p3) → p4) ∨ p5) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h10
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230495271758176503708531709162 : (((True → p1) ∧ p2) → ((((True → ((True ∧ p1) ∧ (((p2 ∧ True) ∨ (p4 → p1)) → (p1 ∨ p5)))) ∧ True) → p3) ∨ ((False ∨ p4) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60454591611930567325250300378 : (((p5 → p1) → (((p5 ∨ (p1 ∨ (((True ∨ True) ∧ False) ∨ False))) → (p3 ∨ p3)) → ((p3 ∧ p2) → ((p1 ∨ (p3 ∧ True)) ∨ p3)))) ∨ p4) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178049329735196928517623019169 : ((((p1 ∧ (p3 ∧ ((False → (True ∧ (True ∧ p4))) ∨ p3))) ∧ p3) → p4) ∨ (p2 ∨ (False ∨ ((((p2 → False) → (True ∨ p5)) ∧ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230948530047701777102583032717 : (((p3 ∧ p5) ∨ True) → ((p5 ∧ (p1 → False)) ∨ ((((True ∨ p3) → p4) ∧ ((True ∧ False) ∧ (((True ∧ True) ∧ p2) ∨ (p1 ∧ p1)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184148793171681052616766364076 : (((False ∨ (p1 ∧ (((p2 → p2) → p2) ∨ (p4 ∨ True)))) ∨ True) ∨ ((True ∨ ((((p4 → (p2 → p3)) ∧ False) → (p4 → p2)) ∨ p5)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227008709954114809837437744745 : (((p1 ∨ p4) → p2) ∨ (((((((p3 ∨ (False ∨ p5)) ∨ ((p5 ∨ p4) ∧ (p1 → (p5 ∨ (p5 ∨ p4))))) ∧ p4) ∧ False) ∧ p3) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147444169814667657002940656710 : ((((False ∧ p3) ∨ ((p5 → ((((True ∧ p4) ∨ (p3 → (p4 ∨ p2))) ∧ (p3 ∨ p1)) → p3)) → p5)) ∨ p4) ∨ (True → (p5 → (p3 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39652872864740283347135325228 : (((p3 ∨ (((p2 → p4) ∨ True) → (p1 → ((((p4 ∧ ((((p5 ∧ p5) ∧ p2) ∨ p5) → (p3 ∧ p5))) ∧ p3) ∨ True) ∨ p4)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157859575731444960497286319193 : (((p4 ∧ ((p5 ∨ p4) → (p4 → ((p2 ∧ False) ∧ p1)))) ∧ (((p3 → p2) → (True → p2)) → p3)) ∨ ((p1 → (True ∨ (p4 ∨ True))) ∨ False)) := by
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
theorem thm_5_vars_97967991668334341628340358734 : ((p4 ∨ (((p2 ∧ True) ∧ ((True → p4) ∧ (((p5 ∧ (p1 ∧ (True ∨ p2))) ∧ ((p4 ∨ p3) ∨ ((True ∨ False) ∨ p2))) → p1))) ∧ p2)) → p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147565842029481090035004949394 : (((((((((((p1 → p2) → (p1 → p1)) ∧ p5) ∧ p3) ∧ p3) → p5) ∨ p4) → (False → p5)) ∧ p4) → p1) ∨ (p5 → (False ∨ (p5 ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191626200748846629854918493342 : ((p3 ∧ (p1 → (((p5 ∨ p2) ∨ p3) ∧ (p3 ∨ p3)))) ∨ (False ∨ (False → ((((p4 → True) → (True → p2)) ∧ (True ∧ p4)) ∨ (p4 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178950566303035040578160071840 : (((p5 ∧ False) ∨ ((False → (((False ∨ (p1 → True)) ∧ True) ∧ p4)) → p3)) ∨ ((((p2 ∧ ((p4 → p5) ∨ (p2 ∨ p3))) ∨ p4) ∧ p3) → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715013078877527029055404929218 : ((((p1 ∨ ((p2 ∧ (p2 → p3)) → p2)) → ((p1 ∧ False) ∨ (p1 ∨ ((p1 ∧ ((True ∧ False) ∨ True)) ∨ (((p3 → p5) ∨ True) ∨ True))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655864827504852923617813380129 : (((((((False ∨ p3) ∨ p5) ∧ ((p5 → p4) ∧ (((True ∧ ((p2 → p5) ∨ p1)) ∧ p3) ∨ p3))) → (p4 ∨ (p5 → True))) ∨ (False → True)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89126987663826520152011385277 : ((((p5 → p5) ∨ p4) ∧ (((((False ∨ (((p2 → (p3 ∧ p1)) → p2) ∨ (p5 ∨ (True ∧ (p4 → p3))))) → p4) ∧ p5) ∨ p4) ∧ p3)) → p4) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h10 : (False ∨ (((p2 → (p3 ∧ p1)) → p2) ∨ (p5 ∨ (True ∧ (p4 → p3))))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h11 := h8 h10
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h19 =>
      -- One of the premise coincides with the conclusion.
      exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2714179304276706953356060986 : ((p2 → ((False ∧ False) ∧ (p2 ∨ True))) → ((((p3 → p4) → (p3 ∧ (p3 → p5))) ∨ False) ∨ ((p3 → ((p2 ∨ False) ∧ p2)) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50662356232598515151442591231 : (((((p4 ∧ ((p1 → p4) ∧ False)) → (p2 ∨ p3)) → ((p3 ∧ p5) ∧ (((p3 ∧ p5) → p5) ∧ False))) → ((p2 → (False ∨ p2)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228549323655737147366236981609 : ((p1 ∨ (p5 ∧ p1)) ∨ (p1 → ((p3 → True) → (((False ∨ p4) ∧ False) ∨ (((p2 → (False → ((p1 ∧ p2) ∧ False))) ∧ (p2 → p4)) ∨ p1))))) := by
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
theorem thm_5_vars_310094661064360041072517300854 : (p2 ∨ (((p4 ∨ (((p1 ∧ p1) ∨ True) ∨ p1)) → ((p5 → (p2 ∨ p5)) ∨ p5)) ∧ (p1 ∨ ((((p4 → p4) ∧ True) ∨ (p3 ∧ False)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769247611784259436497561610312 : (((p5 ∧ ((p5 → p1) ∨ ((p2 → (True ∧ (True ∨ p3))) ∧ ((p4 → ((p4 → False) ∧ (((p5 → p3) → p4) → p5))) ∨ (p3 ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66431344236276599957879674179 : ((p5 ∨ (p5 → (p3 → (p2 → (((((p5 ∧ (False ∨ p5)) ∨ ((p3 → p2) ∨ (p1 ∨ True))) → True) ∨ (p5 ∧ p3)) → (p1 ∧ p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352171819031906266030296955966 : (p4 → ((((p1 ∧ True) ∨ p3) ∨ p4) ∧ ((p5 ∨ p5) ∨ ((p5 ∨ (p4 → (p4 ∧ ((p1 → ((p5 ∨ False) → True)) ∨ (p2 ∨ p5))))) ∨ p4)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317628798354123542257895277945 : (p4 ∨ (((((p3 → ((False ∧ (p5 ∧ True)) ∨ False)) ∨ ((False ∧ p3) → ((p5 ∧ True) ∧ True))) ∧ (False ∨ ((p4 ∧ True) → p5))) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50851934197180776334806628476 : (((((((p1 ∨ p1) ∧ p5) ∨ ((p2 ∧ ((p3 ∨ p3) ∧ p1)) → (p3 ∧ True))) ∨ p4) ∨ True) ∧ (p1 ∨ ((p2 ∧ (p4 ∨ p3)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134098159491036564942267935072 : ((((p3 ∨ ((p3 ∨ p3) → (True ∧ (((True → p3) ∨ p3) ∧ ((p5 ∨ False) ∨ ((p3 ∨ p3) → False)))))) → p2) ∨ True) ∨ ((p2 ∨ p5) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258760358075422459303045869164 : ((True → False) → (((True ∧ p1) ∨ ((p5 → (False ∨ (p1 ∨ ((p4 ∧ ((p3 → p5) ∨ False)) ∧ (((p2 ∨ p5) ∧ p1) ∧ False))))) ∨ p5)) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50225908674848457916028348667 : ((((p1 ∨ (((p5 → (((True → p4) → (False ∨ p1)) → (p4 ∧ (p5 ∧ p2)))) → p3) ∨ p4)) ∨ p1) ∨ (p2 ∨ ((True ∨ p3) ∨ p5))) ∨ p2) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356009785913549630523389834104 : (p5 → (((((p5 → p3) ∨ (p2 ∧ p4)) → (p1 ∨ ((p5 ∧ p2) ∧ ((True → (p2 ∨ True)) ∧ p3)))) ∧ p3) ∨ (p5 ∨ (p3 ∨ (p4 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310599748200107137467363319713 : (p2 ∨ ((p1 → (True ∧ (p1 ∨ p2))) ∧ (((p5 ∧ ((p5 → p5) → (p3 → p5))) ∨ ((True → False) → p1)) ∨ (False ∧ ((p4 ∧ False) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156604222358881715581743286233 : (((((True → ((p5 ∨ (p2 ∧ p3)) ∧ p1)) ∨ ((True ∧ ((True ∨ p5) ∧ p1)) ∨ p5)) ∧ True) ∧ p1) ∨ ((p1 → (p4 → (p2 ∨ p4))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741298512397984734281260730481 : ((((p4 ∨ p5) ∨ (((((((p2 → (p5 ∧ (False ∧ p3))) ∨ p1) → ((p1 → True) ∨ (p2 ∨ p2))) → p3) ∨ p2) → (p4 ∧ p4)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113866255146009224287650868370 : (((p4 → (p5 ∧ ((p5 ∨ ((((p2 ∧ p3) → p2) → True) ∧ p2)) ∨ ((p2 → p1) → ((p1 ∨ p5) ∧ p5))))) → (p1 ∧ p3)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89334182834466262209230540705 : (((p3 ∨ (p1 → p2)) ∧ ((p2 → ((p2 ∨ (p3 ∧ True)) ∧ p3)) ∧ (p1 ∨ (p1 ∧ ((((True → p3) ∨ (p2 → p1)) ∧ True) → p4))))) → p3) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h3.left
    let h13 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h15 : p2 := by
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h17 := h11 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h18 := h12 h15
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h23 : p2 := by
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h24 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h25 := h11 h24
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h26 := h12 h23
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- One of the premise coincides with the conclusion.
      exact h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324355317950048379431934797349 : (p5 ∨ (((True → (p3 ∧ (p1 ∧ p2))) ∧ p4) ∨ (((p2 → p3) → (True → ((True → p2) ∨ (p2 ∨ (p5 ∨ False))))) ∨ ((p2 ∧ p1) → True)))) := by
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
theorem thm_5_vars_336370349070963963017795721141 : (p1 → (((p1 → p5) → (((((p2 ∧ (True ∧ (False → True))) ∧ (False → True)) ∨ ((p5 ∨ p3) ∨ ((True → p2) ∨ True))) → False) ∨ p2)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180382700444830592272650961718 : ((((p3 → (p5 → False)) ∧ ((p4 ∧ (p3 → p4)) ∨ p4)) ∨ (p1 → p1)) → ((False ∧ (((p5 ∨ True) ∨ p3) → p2)) ∨ ((p4 ∧ p3) → p3))) := by
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
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- One of the premise coincides with the conclusion.
    exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709843826788089858505820581535 : ((((p4 → ((p5 → (p2 ∧ p3)) → (True → True))) → ((((p5 ∨ (False ∧ p3)) ∨ (p1 ∧ False)) ∧ p4) ∨ (p5 → ((False ∨ False) → p3)))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136554835569446029529034784344 : ((((p4 ∧ p4) ∨ p5) ∨ ((((p5 ∧ (False ∧ False)) ∧ p1) ∨ (((p5 ∨ p1) ∨ True) ∧ p1)) ∧ (p3 ∨ (p1 ∨ p3)))) ∨ (True ∨ (p1 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117032040489570139342492337065 : (((p2 ∨ p5) → ((((False → p1) ∧ p2) → (p1 ∨ ((((p4 ∨ (p5 → (p5 ∧ False))) → p2) → p2) → p3))) ∨ (p2 ∧ p5))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207408051974410313116187671790 : (((p4 ∧ (p3 ∨ (p5 → p1))) ∨ p1) → ((p3 ∨ False) ∨ (((True → ((p3 → (p2 → p1)) → p1)) ∧ ((True → (p5 ∨ p5)) ∧ True)) → p5))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h10, we can now drive its conclusion.
      let h13 := h10 h12
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h22 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h23 := h20 h22
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111546810526339949669735020717 : (((((((((p5 ∨ False) → ((False → p1) ∨ p3)) ∧ (True ∧ p5)) → (p1 ∧ (p2 ∧ p4))) → p5) ∨ (p5 ∧ p1)) ∧ p4) ∨ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259547458668438207672398845516 : ((p1 → True) → (((((False ∧ p5) ∨ p3) ∨ (((((p2 ∨ ((p3 ∨ (False ∨ True)) ∨ (p3 → False))) ∨ p1) → p3) ∨ True) → False)) → p3) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      exact h7
  case inr h8 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : ((((p2 ∨ ((p3 ∨ (False ∨ True)) ∨ (p3 → False))) ∨ p1) → p3) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62045304125993110283632948838 : ((p2 ∧ ((p1 ∨ p2) ∨ (p2 ∨ ((p1 ∨ (((False ∧ (p4 → ((p3 → (p2 → (False → (p1 ∨ p3)))) ∧ p4))) ∨ False) ∧ p5)) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112938079246413806282053161935 : ((((False → True) → (p3 ∧ ((((p3 → (True ∨ ((p1 ∧ (False ∨ p2)) ∧ p4))) ∧ p3) → (p2 ∨ (p5 ∨ p5))) ∧ p5))) → p4) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179586038480231520340420026661 : ((p3 → ((((p4 ∨ (p3 ∧ p4)) → p1) → (p4 ∧ (p3 ∨ p2))) ∧ False)) ∨ (((False ∧ False) → ((False ∨ (p4 → (p1 ∨ False))) → p2)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324294483244489479144377366591 : (p5 ∨ (((False ∧ ((p5 ∨ p2) ∧ p3)) ∨ (False ∨ p3)) → (True → (True ∧ ((p4 ∨ ((p2 → p3) → ((p5 → (p3 → False)) ∧ p1))) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755256771966332235858761352479 : (((False ∧ (p5 → (((p1 → (p5 ∨ (p4 ∧ True))) → p2) ∧ (False ∨ ((False ∧ p1) ∧ (p5 ∧ ((True ∨ p4) ∧ (p5 ∨ (False ∨ p4))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299204574278238973048957063000 : (False ∨ (((((p4 → False) ∧ ((p3 ∨ ((p1 → True) → p5)) → p1)) ∨ (((p1 → True) → (p4 ∧ False)) → (False ∨ p5))) ∧ (p5 → p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167284616242827056956102892821 : (((((p2 → (False → p5)) ∧ (True ∨ ((p2 → p2) ∨ (p3 → (p3 ∨ p4))))) ∨ p1) → True) → ((((False → p1) ∧ (p3 ∧ p5)) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716740090292018539104249055731 : (((((p4 → p3) → (p1 → False)) ∧ ((p2 ∧ (p1 → ((((p4 → True) ∨ (((p5 ∧ p4) ∧ p5) → (p5 ∧ p4))) ∨ p5) ∨ False))) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_34135046453639995569514827298 : ((True → (((p4 ∧ p5) ∧ ((((((p4 → True) ∧ p5) ∧ (p3 → (p2 → ((p3 ∧ False) → p4)))) ∨ p4) ∨ p4) ∧ (p2 → False))) ∨ True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206905978896695595710722026988 : (((((p3 → p1) ∨ p3) ∨ p5) ∧ p1) → (p1 → (p3 → ((((p4 ∧ True) ∨ (False ∧ True)) ∧ (True ∧ (p3 ∨ ((True → False) ∨ p2)))) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
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
theorem thm_5_vars_115056376244301292191948528956 : ((((p2 ∧ (((False ∨ p5) ∧ (p2 → p2)) ∧ p3)) ∨ (False ∧ False)) ∨ (((False → ((p5 ∨ (p3 → True)) → True)) ∧ p1) → True)) ∨ (p4 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229401271869792495264182948184 : ((p1 → (p2 ∨ p5)) ∨ (((p1 ∧ ((p3 ∧ False) ∨ p4)) ∨ ((p2 ∨ p3) ∨ False)) ∨ (((False ∧ (p2 → True)) ∨ True) ∨ (True ∨ (p1 ∨ p4))))) := by
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
theorem thm_5_vars_299316304475754630868926132507 : (False ∨ (((((p2 → (p2 ∨ p5)) ∧ False) ∨ p5) ∨ (((p2 → False) ∨ (p3 → ((False ∧ True) ∨ False))) ∨ ((p3 ∨ (p5 → True)) ∨ True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112159884126540521626668121539 : (((p2 ∧ (False ∨ (p4 ∨ (((((p1 ∨ p3) ∧ p1) → (False ∨ p4)) → ((p1 ∧ p5) ∨ p4)) ∧ (p4 ∧ (False ∨ p1)))))) ∨ True) ∨ (p1 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354784217122899374800606533135 : (p5 → ((((p1 ∨ p1) ∧ (((p1 ∧ False) ∧ p4) ∨ p5)) ∨ (((((True → p4) → False) ∨ True) ∨ p4) ∨ (True ∨ ((p4 → p1) ∨ p2)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_157885575459566686656789806998 : ((((True → p1) → ((p3 ∨ p2) ∨ ((p4 → p3) ∧ p4))) ∨ ((p2 → ((p5 → p3) ∨ p3)) → p3)) ∨ ((True ∨ ((p4 ∨ True) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158591373112818688814429400027 : ((False ∧ (((False ∧ ((((p3 ∨ p2) → p4) ∨ (False → (p3 → (True ∨ p5)))) → p1)) ∧ p5) ∧ p2)) ∨ (False → (p2 → (p1 → (True ∧ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205224905307663552485250013037 : ((((p2 ∨ p5) ∧ p4) ∨ (p4 ∨ False)) ∨ (p4 ∨ (((p5 → p5) → ((((((False ∨ (p5 ∨ True)) ∨ True) ∨ True) → p4) ∨ p1) → True)) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228071504078562904125398416293 : ((p4 ∧ (p4 ∧ p2)) ∨ (((True ∧ ((p4 ∨ (((p4 ∨ p2) ∨ (p2 → ((p3 ∨ p3) → False))) → (p4 ∨ True))) → p3)) ∨ (False ∨ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153799122839676258300790759327 : ((p5 → ((((((((True ∨ p2) ∨ False) → ((False ∧ False) → p3)) ∨ p1) → p4) ∨ p3) → (p2 → p5)) ∧ p1)) → (p5 → (True ∧ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



