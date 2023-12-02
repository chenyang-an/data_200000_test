variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83316820432661471329948970667 : (((((True ∨ p2) → ((p4 ∧ p1) ∧ p2)) ∧ (((p4 ∨ p1) → p4) → ((True ∨ False) ∧ True))) ∧ ((p4 ∨ (p5 → p4)) ∧ (p1 → False))) → p5) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : p1 := by
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We need to get the right conjuct of h12 based on <expert-advice>.
      let h13 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h14 := h7 h9
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : p1 := by
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h17 : (True ∨ p2) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h18 := h4 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h21 := h7 h16
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226777992009382919803297351864 : (((p2 ∧ p5) → p1) ∨ (p4 ∨ ((((True ∧ (p5 ∨ (True ∧ ((p1 ∧ (p4 → p2)) ∨ (p3 ∧ p5))))) ∨ (p3 ∨ p4)) ∧ (p4 ∧ False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178683528362917760021563096911 : (((((p3 ∧ p3) → False) ∧ False) ∨ ((p4 → p3) ∨ ((p5 → p3) ∨ p1))) ∨ ((p4 ∨ (p2 ∨ True)) → (((False ∧ (p1 ∧ p5)) → p5) ∨ p5))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241589567728412734708920975219 : ((False → p4) ∧ (((p1 ∨ True) ∧ (p4 ∧ (p4 ∨ (p3 → ((p5 ∧ (((p3 ∨ p4) ∨ p5) ∨ p2)) ∨ (True → (p5 ∧ p2))))))) ∨ (True → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2414012281240837408394612413 : ((True → ((((p3 ∨ (p4 ∨ p1)) ∨ p3) → (p3 → p1)) ∨ p2)) → (p3 → ((p5 → (((p4 ∨ p2) → (p4 ∨ p4)) ∨ p5)) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810753745028903875046404581969 : (((p5 → ((p3 → (p5 ∨ False)) → (p1 ∨ (p4 ∨ (((((p4 ∨ False) ∧ True) ∨ ((False ∧ (p3 → p2)) ∨ False)) ∨ (True ∨ p5)) ∨ True))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_179909575093846590806770152283 : (((((p4 ∨ (False ∧ p5)) ∨ ((p5 → p4) → (p3 ∨ p5))) ∨ p1) ∨ p2) → ((p1 ∧ (p2 ∧ ((p1 ∧ (p3 ∨ p2)) ∨ p3))) ∨ (False → p2))) := by
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h6
          -- False on the left can always be used.
          apply False.elim h6
        case inr h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- False on the left can always be used.
          apply False.elim h8
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- False on the left can always be used.
        apply False.elim h11
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h15
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664744386260232721516313824584 : ((((False → (p1 → (p1 → (((p2 ∧ p1) → ((False → p4) → (False → True))) ∨ (p3 ∨ (((True → p3) ∨ p2) → p5)))))) → (p3 ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85299398375757195302528292103 : ((((p5 ∨ ((False ∧ False) ∨ (((p1 ∨ p5) ∧ True) ∨ p2))) ∧ p4) ∧ ((p4 → (True ∧ (False ∧ (False ∧ p4)))) ∧ (p5 ∨ (True ∧ False)))) → p1) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h3.left
          let h27 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h27
          case inl h28 =>
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- False on the left can always be used.
            apply False.elim h31
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h3.left
          let h34 := h3.right
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
            have h36 : p4 := by
              -- One of the premise coincides with the conclusion.
              exact h5
            -- We have shown the premise of h33, we can now drive its conclusion.
            let h37 := h33 h36
            -- We need to get the right conjuct of h37 based on <expert-advice>.
            let h38 := h37.right
            -- We need to get the left conjuct of h38 based on <expert-advice>.
            let h39 := h38.left
            -- False on the left can always be used.
            apply False.elim h39
          case inr h40 =>
            -- Conjunctions on the left can always be decomposed.
            let h41 := h40.left
            let h42 := h40.right
            -- False on the left can always be used.
            apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h3.left
        let h45 := h3.right
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h46 =>
          -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
          have h47 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h44, we can now drive its conclusion.
          let h48 := h44 h47
          -- We need to get the right conjuct of h48 based on <expert-advice>.
          let h49 := h48.right
          -- We need to get the left conjuct of h49 based on <expert-advice>.
          let h50 := h49.left
          -- False on the left can always be used.
          apply False.elim h50
        case inr h51 =>
          -- Conjunctions on the left can always be decomposed.
          let h52 := h51.left
          let h53 := h51.right
          -- False on the left can always be used.
          apply False.elim h53



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65718411534821370547355463428 : ((p4 ∨ ((True ∧ (p3 ∧ (True → (((True → (p4 ∧ (p3 → False))) ∨ (p5 ∨ (((p4 ∨ p1) → p1) ∨ p2))) → p5)))) ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303832958684505248264685177269 : (p1 ∨ (((p3 → (True → ((((False → p4) ∧ (p1 ∨ (True ∨ True))) ∧ p2) → (((p3 → (p5 ∨ p2)) ∨ p4) → p1)))) ∧ (p2 → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260841408160667972887593845039 : ((p4 → True) → ((p4 → (p5 ∨ (p2 ∧ (((((p1 ∧ p5) ∧ (True ∧ ((True → p2) ∧ p3))) → p4) ∨ (False ∧ False)) ∧ p4)))) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243282094364637340948730563551 : ((p4 → p4) ∧ ((((True ∧ (p1 → False)) ∧ (((p4 → p1) → ((p3 ∧ (((p2 ∨ p1) ∨ p4) → p4)) → False)) → (p3 ∨ p3))) ∧ p1) → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h10 := h8 h9
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58324879314483689713042291159 : (((False ∨ False) ∧ (False ∧ (((p2 → p3) ∨ p5) ∧ (p2 ∧ (p4 ∨ ((p5 → p4) ∧ ((((p1 ∨ True) ∧ False) ∨ False) → (p5 ∨ p1)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157373643822125277477290097664 : (((p5 → (((p3 ∨ ((True ∨ p3) ∨ (p5 → False))) ∧ (((p5 ∨ p2) → False) → p4)) → p3)) → p4) ∨ (True ∨ ((p3 ∧ False) ∧ (True ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44224310988616748832763098556 : ((((((True → (True ∨ (((True ∧ p5) ∨ (p5 → ((True ∧ p2) → False))) → p3))) → p5) → True) ∨ (p3 ∧ ((True ∧ p5) ∨ p4))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43330249527007059438897437899 : (((((((p1 → ((p4 ∧ p2) → (((p5 ∧ (p3 → p1)) ∧ (p1 ∧ p1)) ∨ p4))) → (p2 ∧ (p2 ∧ p5))) → p5) → False) ∨ p5) → p5) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p1 → ((p4 ∧ p2) → (((p5 ∧ (p3 → p1)) ∧ (p1 ∧ p1)) ∨ p4))) → (p2 ∧ (p2 ∧ p5))) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h5 : (p1 → ((p4 ∧ p2) → (((p5 ∧ (p3 → p1)) ∧ (p1 ∧ p1)) ∨ p4))) := by
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h10 := h4 h5
      -- We need to get the right conjuct of h10 based on <expert-advice>.
      let h11 := h10.right
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h3
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150921669482852604547264369078 : ((((False → True) ∨ ((True ∨ True) ∧ (((False ∨ p3) → (p2 ∧ (p1 ∨ (False ∧ (True ∧ True))))) → p4))) ∨ p1) → ((p1 ∨ (p5 ∧ p5)) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
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
theorem thm_5_vars_90921172675038384125511027973 : (((True → False) ∧ ((p1 ∨ ((p2 ∧ (p2 ∧ (p3 ∨ False))) ∨ False)) ∨ (((((p3 ∧ p4) ∨ ((True ∧ p5) ∨ p4)) ∧ False) → False) ∨ p2))) → p1) := by
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
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h13 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h14 := h2 h13
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h22 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h23 := h2 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260791874152096494066581588785 : ((p3 → p5) → ((p1 → (((p2 → (p4 ∨ p3)) → (True → p2)) ∨ p1)) ∨ (p5 → ((True ∧ (((False ∧ True) ∧ False) → False)) ∨ (p1 → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326831332240002416877821415827 : (True → ((((p4 ∨ (((p2 → (((p4 ∨ p3) ∨ p1) ∧ (p5 ∨ False))) ∧ ((p5 → (False ∧ p1)) ∨ p5)) ∨ p4)) ∧ (True ∧ False)) ∧ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113069637009145287702611955465 : (((p3 ∨ (((p4 ∨ ((((p1 ∧ (p1 → (p1 → False))) → p4) ∧ False) → (p4 ∧ True))) ∨ p4) ∨ (p2 ∧ (p5 → p1)))) → p3) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32855293305580394687266361084 : ((p3 ∨ (((p4 → ((p3 → ((p1 → p2) ∧ False)) ∧ p3)) → ((p5 ∨ (p3 → p5)) → ((p1 ∧ p4) ∧ ((False → p1) → p1)))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_178008406238984996064038114530 : (((p4 ∨ ((p4 → (((p2 ∧ True) → p2) → p2)) → (p4 ∧ p5))) ∨ p3) ∨ (False → ((p5 → p4) ∨ (p4 ∧ ((p1 ∧ (p4 ∧ True)) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129301996657872886222397263923 : (((((True ∧ p3) ∨ p3) → (((True ∧ False) ∧ False) ∨ (((((p2 ∨ (p3 ∨ True)) ∧ False) ∧ p5) ∨ True) → True))) ∨ p1) ∧ (False ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656484932808021278280592803817 : (((((((True → (p4 ∨ p4)) ∨ ((False ∧ p4) ∧ p1)) ∨ p2) → ((((p2 ∨ p2) → (False ∨ (p3 ∧ p3))) ∧ False) ∨ p5)) ∨ (p5 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111897026032940242162141806425 : ((((p5 ∧ ((p3 → ((((p3 ∨ p1) → p4) ∨ False) → False)) ∨ (p3 ∧ False))) ∨ ((((p2 → p4) ∨ p3) ∧ False) ∨ p4)) ∨ p2) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234318204164586261897149110456 : ((p1 → (p2 ∧ p1)) → (((((p5 ∧ ((p3 ∨ p4) → p3)) → (p5 ∨ p1)) ∧ p3) ∧ (True ∨ ((True → True) → False))) → ((p3 → p2) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h9 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h13 := h3 h12
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746366200578594555538803650986 : ((((p2 ∨ False) → (p3 ∨ (((((p5 → (True → p5)) ∨ (p5 → p1)) → ((p5 ∧ False) ∧ (p1 ∨ p1))) → (False ∧ p3)) → (p2 → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260084973834772462622823230227 : ((p2 → False) → (p3 ∨ ((p3 ∨ (((True → p5) → True) ∧ (p1 ∨ ((True ∨ True) ∨ ((p1 ∨ p2) ∨ p3))))) → (True ∧ ((p5 → p3) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    cases h6
    case inl h7 =>
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
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51276033608978239697459532589 : (((False ∧ ((False → (p1 ∨ p5)) ∧ (p3 ∧ (((p4 ∨ (p3 ∧ (True ∨ False))) → p1) ∧ p4)))) ∨ (p1 ∨ (False → ((p5 ∧ p5) → True)))) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136122436337680298247944957456 : (((p4 ∨ ((p2 ∧ (p1 ∨ (p4 ∨ p5))) ∧ p4)) ∨ ((((p4 ∨ p1) ∨ ((p1 → True) ∨ p1)) ∨ (p5 ∧ True)) ∧ p3)) ∨ ((True ∧ p1) → p1)) := by
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
theorem thm_5_vars_191252704177028123562573228945 : (((p2 ∧ p4) ∧ ((p1 ∨ (p5 ∧ False)) ∨ (p5 ∨ False))) ∨ (p1 ∨ ((((False ∧ p3) ∧ (p1 → (p5 ∧ True))) → ((True ∨ False) ∧ True)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175086035273874107862474094078 : ((p3 ∧ ((p1 ∧ p3) ∨ (((False ∧ ((p4 → (p4 → p1)) ∨ False)) ∧ p5) → True))) → (((p1 → ((p2 ∧ p1) → p2)) → False) → (p5 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : (p1 → ((p2 ∧ p1) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h8
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h15 : (p1 → ((p2 ∧ p1) → p2)) := by
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h20 := h2 h15
    -- False on the left can always be used.
    apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47350788783310379553650240161 : ((((p5 → p2) ∧ (((p4 ∧ p5) → (p1 → (p3 → (((True ∨ p5) → p2) → ((True ∧ False) ∧ p5))))) → (p2 ∧ True))) ∨ (False → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59557613693442064649840225506 : (((p3 → p2) ∨ (p3 → (((p3 ∨ p5) ∨ (False ∨ (p4 → p5))) → ((p1 ∨ p1) ∧ ((((p4 ∨ (p2 → p1)) ∨ p2) ∨ True) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111321954830049867829635465223 : (((p1 ∧ (p5 ∧ (p5 ∧ ((((False ∧ ((((True ∨ (p1 ∧ (True → p1))) ∧ p2) ∨ p3) ∧ p2)) ∧ p3) ∨ True) ∧ p3)))) ∧ False) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253137206064972372303624381343 : ((True ∧ p5) → (((p3 ∧ p1) ∨ ((p2 → (p4 ∨ ((p1 ∧ (p2 ∧ False)) ∨ p3))) ∧ p5)) ∨ (p4 → ((p1 → ((p4 → p2) ∧ p4)) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2879187699840134307709077854 : (((True ∧ p5) → p5) ∧ (((((((False ∨ p1) → (p4 ∨ p2)) ∧ p4) ∧ p2) ∨ (((p5 ∧ p4) → p1) ∨ True)) → p4) ∨ (p4 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137110155820818234968361680968 : ((True ∧ ((p3 ∨ (((p4 → ((p4 ∨ True) ∨ (p1 → False))) → (p2 → p3)) ∨ False)) → ((p3 ∧ p5) ∧ (p2 → p5)))) ∨ ((p2 → p2) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177838150902314201415732755680 : (((((p3 ∨ ((p5 ∨ (p1 ∧ p1)) ∨ True)) → (False → False)) ∧ p2) ∨ p1) ∨ (p1 ∨ (p2 ∨ ((False ∨ ((p5 ∨ (True ∨ True)) ∨ p2)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144516552575914336866741834795 : ((((((((p5 → p3) → ((p1 ∧ p2) ∧ p3)) ∨ p5) → False) → (p3 ∨ (p3 → p3))) ∨ p4) ∨ (p5 → p5)) ∧ ((True ∨ False) ∨ (p4 ∧ p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198404594734019982765238496726 : ((p4 ∧ ((p2 ∧ (False ∧ (p5 → False))) ∧ p1)) ∨ ((False ∨ (p4 ∧ ((p3 ∧ p5) ∧ (((p3 → p3) ∧ True) ∨ (True ∧ (p2 ∧ True)))))) → p3)) := by
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
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356379769725683097589039475126 : (p5 → ((((False → p3) ∧ ((True ∨ (p1 ∧ p3)) ∨ (False ∧ False))) ∧ (p5 ∨ p2)) → ((((p2 → True) ∧ p1) → p3) → ((p3 → False) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260713671374062544180983155761 : ((p3 → p4) → ((((True ∧ (p1 → ((p5 → p5) ∧ (((p1 → p2) ∧ p4) ∧ p3)))) → p4) ∧ (p2 ∧ ((False ∨ p5) → (p2 → p4)))) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616261811426314705843178213961 : ((((((True ∧ ((p4 ∨ p5) ∧ (((p3 ∨ p3) ∧ p5) ∨ p1))) ∨ True) ∨ (p5 ∧ (((p3 ∧ False) ∨ p2) ∧ (p4 ∧ (True ∧ p3))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114021971636600237015619930557 : (((((p4 ∨ p2) → ((True ∨ False) → (((True ∧ ((False → p2) → (True → True))) ∧ p1) → p2))) ∨ p1) ∨ (p3 ∨ (True ∧ False))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49121988914967227002222876938 : (((((False ∨ ((((p4 ∨ (p1 ∧ p3)) ∨ False) → True) ∨ p1)) ∧ True) ∧ (p1 ∨ (False ∧ (True ∧ (p4 → p3))))) ∨ (p2 ∨ (False → True))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178920415810925801543990716642 : (((p2 → True) ∧ (p3 → (p3 ∧ (p5 → (False ∧ ((p3 → True) ∨ p5)))))) ∨ ((p4 → p3) ∨ (p2 → (((p4 ∧ p5) ∨ (p4 ∨ True)) ∨ True)))) := by
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
theorem thm_5_vars_303990479260326337028337625089 : (p1 ∨ (((p1 ∧ p2) ∨ (p1 ∨ ((p4 → ((p5 → (p3 ∧ p2)) ∧ (p2 → p5))) ∧ (p5 ∧ ((True → (p3 ∧ (p4 ∧ False))) → p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123252833059948011062306296395 : ((((p1 → False) ∨ (((True ∨ (((p1 ∨ (p4 ∧ p3)) → True) ∧ True)) ∨ (p3 ∧ p5)) ∨ p1)) ∧ (False ∨ (p4 ∨ (p1 → False)))) → (False ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
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
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h13 =>
            -- False on the left can always be used.
            apply False.elim h13
          case inr h14 =>
            -- Disjunctions on the left can always be decomposed.
            cases h14
            case inl h15 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h20 =>
            -- False on the left can always be used.
            apply False.elim h20
          case inr h21 =>
            -- Disjunctions on the left can always be decomposed.
            cases h21
            case inl h22 =>
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
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h27 =>
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- Disjunctions on the left can always be decomposed.
          cases h28
          case inl h29 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h30 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h32 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h35 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119502740107217873226569112287 : ((p4 → (p4 → (((True ∧ ((p2 ∧ p3) → p2)) → p1) → ((((p1 ∧ p2) ∧ p2) ∧ (p3 → ((p5 → False) → p4))) ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_132940213217914551751784701432 : ((p4 ∨ (((((False → (True ∧ (p1 → False))) ∧ ((True ∧ p3) → p5)) → p2) ∨ (True ∧ p4)) ∨ ((p4 ∨ p5) ∨ True))) ∧ (True ∨ (p2 ∧ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783210010372406213518850134115 : (((p3 ∨ (((p1 → (((False ∨ p1) ∨ ((p2 ∨ p5) ∧ False)) ∧ (p1 ∨ ((p3 → (True ∧ True)) ∨ p4)))) ∨ p5) → (p3 ∨ (False ∨ True)))) ∨ p1) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256143080461362063813240843900 : ((True ∨ p5) → (p3 → ((p4 ∧ (p5 ∨ ((p4 ∨ ((p1 ∨ ((p3 ∨ p4) → p3)) ∨ ((p5 ∨ p5) ∨ (True → False)))) ∧ True))) ∨ (p5 → p5)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690988033131312440696619133638 : ((((((p5 ∧ p2) ∧ ((((p4 → (p4 ∨ p1)) → p5) ∧ p2) → p4)) → (p2 → p4)) → ((p1 ∨ p3) ∧ (False ∧ (p4 ∧ (False ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253617397734973729335473340279 : ((p1 ∧ True) → ((((p4 → (((True ∨ True) ∧ p5) ∧ (p3 ∧ p2))) → ((p3 → p3) ∧ p2)) ∧ (p5 → (p1 ∧ False))) ∨ ((p1 ∨ True) → p1))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774772045096596560354315851163 : (((False ∨ ((p5 → (((p5 → False) ∨ p5) ∨ True)) ∧ (p5 → (p5 ∧ (((p3 ∧ (p2 → p3)) ∨ p5) ∧ (((p4 ∧ p3) ∨ p5) ∧ False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157029245053911270960272164544 : ((((True → p1) ∨ (p3 ∧ ((p5 ∧ (False ∧ p4)) ∨ ((False ∧ (p2 ∨ (p2 → p1))) → p1)))) ∨ p5) ∨ (((True ∨ (p3 → p4)) ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171487888116413561484677447849 : (((p1 → ((p4 ∨ ((p4 ∨ False) ∧ (p3 ∧ (False → (p2 → p5))))) ∨ True)) ∧ p3) ∨ (p3 → (((p4 ∨ p2) ∨ ((p2 ∧ p5) ∧ False)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310505532038607379229178193757 : (p2 ∨ (((p3 ∨ p5) → (p5 ∨ (p4 ∧ p3))) ∨ (((((p2 ∧ (((p1 ∧ p1) ∧ (p4 → p1)) ∧ p4)) ∨ p4) ∧ True) ∨ (p3 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245812488549901354843886095863 : ((p3 ∧ p3) ∨ (p2 ∨ ((True → (p1 → (((p4 ∨ (True → (((p3 → p2) → p4) ∨ p5))) ∨ True) ∨ ((p3 → False) → (p4 ∨ p1))))) ∨ p2))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730619664402987350328779982834 : ((((p2 ∧ (p3 ∨ p4)) → (True → ((((((True ∧ (False ∨ ((p1 ∨ p3) ∧ p2))) ∧ p1) ∨ p4) → (p5 → False)) ∨ p3) → (p1 ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136205401044438722494748388024 : (((p3 ∨ (((p3 → p5) ∧ p1) → False)) ∧ (((p1 → (((p1 → p1) ∧ (p3 ∧ p1)) ∧ p1)) ∨ (True → p2)) ∧ p1)) ∨ ((p1 ∧ False) → p4)) := by
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
theorem thm_5_vars_209419895246007578566791170334 : ((p2 → ((p2 ∨ (p2 ∧ p4)) ∨ p3)) → (((((((p3 ∧ p2) → True) ∨ True) ∧ (p1 → ((p3 ∨ (False ∧ False)) ∧ p1))) ∨ True) ∨ False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337955909211511390954728885162 : (p1 → (((p5 ∧ False) ∨ (p2 ∨ (p1 ∧ (p4 ∨ ((p5 ∧ p5) ∨ p1))))) ∨ (((p1 → False) ∧ ((p5 ∧ (p5 ∧ (p2 ∧ p4))) ∧ p3)) ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260726712906536333964544999219 : ((p3 → p4) → ((((((p5 ∨ p1) ∧ False) ∧ (p3 → True)) ∨ ((p3 → (False ∧ True)) → p2)) ∨ p2) ∨ (True ∨ ((p3 → p2) ∧ (p3 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113967166783570671666274743549 : (((p1 ∧ ((((p1 ∨ ((p4 → p1) → p2)) ∨ ((p3 ∨ (p2 ∨ (p4 → p3))) ∧ p4)) ∧ p5) ∨ p2)) ∧ ((p1 ∨ p3) ∨ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648660468204190926579758284552 : ((((((False ∧ False) ∧ ((((p2 ∧ p4) ∨ (((True ∨ p2) → p1) → (p1 ∧ (p3 ∧ p1)))) → p1) → (p5 ∨ p3))) ∨ p4) ∧ (p4 → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135142257758762320163449517459 : (((p2 ∨ (p3 ∨ (((p2 → False) ∧ True) → (p2 ∧ ((True ∨ p3) ∧ (False ∨ ((False ∧ True) ∧ p1))))))) ∨ (p2 ∧ False)) ∨ (True ∨ (False ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231054178768300159099482069844 : (((True ∨ p2) ∨ p5) → ((((p5 → (p3 ∨ ((True ∨ p1) → p2))) ∧ (True ∨ p3)) ∨ (((((False → p1) → p2) → p5) ∨ p4) ∨ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111844146629614599666184006932 : ((((p5 → ((p5 ∧ (True ∧ p3)) ∧ (True ∧ (p4 ∨ (p4 ∨ ((False ∧ (p4 → p2)) → p5)))))) ∨ (p5 ∨ (p1 ∧ p4))) ∨ True) ∨ (p2 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217955210106934087336089390960 : (((p1 ∧ p2) ∧ (p4 ∧ p2)) → ((((((p3 ∨ p2) → p3) ∨ (((p3 ∧ ((p3 ∨ False) → p4)) ∨ True) → p3)) → (False ∧ p5)) ∨ p1) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h8.left
  let h11 := h8.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h9.left
  let h13 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38544409703760562123970553217 : ((((((p3 ∧ p5) ∨ p5) ∧ (((p1 ∨ p5) ∧ p4) ∧ False)) ∧ (p1 → (((((p4 → False) ∨ p3) → (p2 ∧ p4)) ∧ p2) → p5))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633470914999532137765808391975 : (((((((p1 → (p2 ∨ ((False ∨ (p1 ∨ (p2 → p4))) ∨ (p3 → p2)))) ∨ (p4 ∧ p3)) ∧ ((True ∨ False) ∨ p5)) ∨ (p1 → p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632285032874328404796138572190 : (((((p2 ∧ ((True ∨ (p1 ∧ False)) → ((((p2 → ((p3 → p4) ∧ p2)) ∧ ((False ∧ (p3 → p5)) ∨ p2)) ∧ p2) ∨ p4))) → p2) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320392719180185034681852493060 : (p4 ∨ ((p1 ∧ p3) → ((((p3 → (True ∧ p3)) ∧ (p1 ∨ False)) → p4) → ((((False ∧ p1) ∧ ((p5 → (False ∧ p3)) ∧ p1)) ∨ True) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177723625299708191201492130602 : ((((p2 ∧ ((p2 ∧ p1) ∧ p3)) ∧ ((False → p4) ∨ (p2 ∧ False))) ∧ p3) ∨ (((p3 ∧ p2) ∨ True) ∨ ((p3 → True) ∧ (p1 ∨ (p2 ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158708690747450529649669514055 : ((p3 ∧ ((((((False ∨ p4) → p2) → p2) ∨ p1) → (((p1 → p1) ∧ p4) ∧ (p3 ∨ p5))) ∨ p2)) ∨ (p5 → (p5 ∨ (p5 → (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615540056761587879349468577439 : ((((((((True ∧ p5) → p5) → p3) ∨ ((p2 ∨ (((p4 → False) ∨ p1) → False)) ∨ False)) → (p4 → ((p5 → p3) → (p2 ∧ p1)))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248739275506354924408801637436 : ((p3 ∨ p3) ∨ ((((p5 ∨ (p4 → (p2 ∧ p2))) ∧ p3) ∨ (p2 → ((p3 ∨ True) → (((True ∧ ((p4 ∨ p1) ∧ p2)) ∨ p2) ∨ p2)))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137177957086087714655242786029 : ((False ∧ ((((p5 ∨ p2) ∨ (p3 → (p1 ∨ p3))) → ((False ∧ p5) ∨ p5)) → ((False ∧ (p4 ∨ True)) ∨ (p4 ∨ p3)))) ∨ (p5 → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39188716350469329748641577908 : ((((p4 → False) → (p4 ∨ ((((((p2 ∧ p5) ∨ ((p4 ∧ ((p2 ∨ p4) ∨ True)) ∨ p1)) → (True ∧ p4)) ∧ p2) ∧ True) ∧ p4))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110971201026970796173520885911 : ((((((((True ∧ p4) ∨ (p1 ∨ (p1 ∧ p4))) ∨ ((p4 ∧ p5) ∧ ((p4 ∧ True) ∨ p1))) ∨ p2) ∧ p1) → (False ∧ False)) ∧ p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328989143558180560242961260486 : (True → (((p2 ∨ (p3 ∨ p1)) ∧ (False ∨ p4)) ∨ (p3 ∨ ((p3 ∧ p1) → (p5 → (((p3 ∨ ((p2 ∧ p4) ∨ (p5 ∧ p1))) ∨ p5) ∧ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_337516024304812129939352548843 : (p1 → ((((((p5 → (False ∧ ((p2 → ((False → p4) → (True → False))) ∨ p3))) → p2) → p4) → p5) ∧ False) ∨ ((p2 ∧ False) → (p3 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_593427084981573794628924874249 : (((((((p2 ∨ (p5 ∨ p5)) → (((p2 ∧ ((True ∨ True) ∧ p3)) ∧ p2) ∨ False)) → ((p5 ∧ False) ∨ False)) → (True ∧ (p4 → p5))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172417399084075050056981709869 : ((((p4 ∧ (p4 ∧ p2)) → False) ∧ ((p1 → False) ∨ (((False ∧ True) ∨ False) ∨ False))) ∨ ((False ∧ (p2 ∨ ((False ∧ p2) → True))) → (p4 → p2))) := by
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
theorem thm_5_vars_118137728882247540418719596095 : ((False ∨ (((((p1 ∧ p5) → p5) → p1) ∨ (True ∧ (((p3 ∧ True) → (False → p4)) ∨ False))) ∨ (p1 ∨ (p2 → (p3 → p2))))) ∨ (p5 ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180371212634344974168856631282 : ((((False ∧ (((p1 ∨ False) → False) → p4)) ∧ (p1 ∨ True)) ∨ (p5 ∧ p4)) → ((p2 → ((False ∧ (True ∧ p5)) ∨ (p1 ∧ (p2 → p1)))) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158053576305418063207710347904 : (((True ∧ (((p2 ∨ p1) ∧ True) ∧ True)) ∨ ((p3 ∨ (False → (True ∨ (p4 → p2)))) → (False ∨ p4))) ∨ (((p4 ∨ (False → p1)) → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140635369310856364310132709611 : (((p3 → ((((p5 ∧ p5) → p5) ∨ True) ∨ (p3 ∧ (p1 ∨ ((p5 ∧ p1) → p4))))) → ((p5 ∧ False) ∧ (p4 → p1))) → ((p2 ∨ p1) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → ((((p5 ∧ p5) → p5) ∨ True) ∨ (p3 ∧ (p1 ∨ ((p5 ∧ p1) → p4))))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256943773054585389585434404069 : ((p1 ∨ p5) → ((((p2 ∧ p3) ∧ p1) ∨ ((((True ∨ (p1 ∨ p2)) ∨ p1) ∨ (False ∧ (True → p5))) ∧ (p4 ∧ (p2 ∧ (True ∨ p4))))) ∨ True)) := by
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
theorem thm_5_vars_48485810609181832872937585032 : ((((p1 ∧ (p1 ∨ (((((True → (((p5 → (False ∧ p1)) ∨ p3) → p4)) → p3) ∧ p1) ∨ False) ∨ p1))) ∧ False) ∧ (p1 → (p4 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112751688104936028953140204108 : ((((p3 ∨ ((p2 ∧ (((True ∨ p5) ∧ True) ∧ (False → p1))) ∨ p3)) → (False ∧ (p1 ∨ ((p5 ∨ p2) → (p3 ∧ p4))))) → p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133898499272764268095816939195 : (((p1 ∨ (((p4 ∧ p4) ∨ ((((((True → p3) → p4) → True) ∨ p5) ∧ p3) ∨ (False ∨ (p3 ∧ p4)))) ∧ p3)) ∧ True) ∨ (True → (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157081666919480796465106772253 : (((p3 ∨ (False ∨ (p5 ∧ ((False ∨ (((p1 → p2) ∧ p5) ∨ (True ∧ (False ∨ p4)))) ∧ p3)))) ∨ p5) ∨ (p3 → (((False ∧ p2) ∧ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793723085128068426524252200834 : (((True → (True → (p5 → (((p2 ∨ ((False ∨ (p2 ∧ p2)) ∧ ((((p2 ∨ p2) ∨ (p2 ∧ (p4 ∨ p3))) → p3) → p3))) ∨ p4) ∨ p5)))) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188131536912120469159850087258 : (((((p3 ∨ p4) → ((p3 ∧ False) ∧ p3)) ∨ p2) ∨ True) ∧ ((((p1 ∧ False) ∨ (True → (((False → (p3 ∧ p4)) → p2) → p1))) ∧ False) → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589158817026196970080685860185 : (((((((p3 → ((p2 → p2) ∨ (p2 ∧ (((((p1 → (False → p4)) ∧ p3) → p2) ∧ p2) ∧ (p1 → True))))) ∧ p1) ∧ p1) → p3) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



