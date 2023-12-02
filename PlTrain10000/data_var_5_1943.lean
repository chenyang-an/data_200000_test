variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340854239125845136262274938545 : (p2 → ((((True ∨ ((False ∧ p1) → (((p5 → (p1 ∨ True)) ∨ (p4 ∧ True)) ∧ (p4 ∧ True)))) ∨ (p2 → p3)) → (p1 ∨ (p4 → p1))) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305865439567882057049481636538 : (p1 ∨ ((((p5 → (p2 ∧ p1)) → p3) ∨ False) ∨ (p5 → (((((p5 ∨ (p1 ∧ p5)) ∧ (p1 → True)) ∧ (p3 ∨ p1)) ∨ (True ∨ False)) ∨ False)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178305718913801803775983146756 : (((((p2 ∨ p4) ∧ ((p4 ∧ (p1 → p4)) ∨ p3)) ∧ p3) ∨ (False ∨ False)) ∨ (((p3 ∧ (False ∧ p1)) → p5) ∨ (((p3 ∧ p4) → p3) → False))) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149991503768972442118815914298 : ((p4 ∨ (p1 ∨ ((p2 ∨ (p2 ∨ (p4 → (True ∧ True)))) ∧ (((p3 ∧ p5) → (p1 ∨ (False → p1))) → False)))) ∨ ((p1 → p1) → (p2 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190037686683952180485518209168 : ((((((p3 → (False ∨ p1)) ∨ True) → p3) ∨ p2) ∧ p1) ∨ (((((((True ∧ True) ∧ False) → p1) → ((p1 ∨ p3) ∧ p1)) ∧ p3) ∨ True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171145797627001382730700372351 : ((p1 → (((p1 ∧ ((p2 ∧ (p5 → (True ∧ p5))) → (p1 → p3))) ∨ False) ∨ p1)) ∧ ((p4 ∨ ((p1 ∧ ((p5 ∧ p2) → p4)) ∨ True)) ∨ False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200344038217510477922533734898 : (((p4 ∨ p1) ∧ ((True ∨ (p2 → p1)) → False)) → ((((True → p3) ∧ p3) ∧ (p5 ∧ p4)) ∨ (p5 → ((p2 → False) → ((p1 → p2) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (True ∨ (p2 → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : (True ∨ (p2 → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807623769942308809630692757506 : (((p4 → ((((p5 ∨ p1) ∨ p3) ∨ p1) → (((((p4 ∧ (p1 → ((p5 → p4) → (p2 ∨ False)))) ∨ False) ∨ (False → p5)) ∨ True) ∧ p4))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h1
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135177182002003344824918838917 : ((((((((p4 ∧ p2) ∨ True) ∨ ((p2 ∨ (True → p1)) ∧ p1)) ∨ (False ∨ p3)) → (p5 ∧ True)) ∨ p2) → (p1 ∨ p2)) ∨ (p3 → (p3 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136554898222942076889279928438 : ((((p4 ∧ p5) ∨ p3) ∨ ((p5 ∧ (p2 ∨ (p3 ∨ p3))) ∨ ((p5 ∨ (((True ∨ p5) ∨ p5) ∧ (True ∨ p2))) → True))) ∨ (True ∨ (p3 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58304307914126013633229328573 : (((True ∨ p4) ∧ ((p4 ∨ ((p4 ∧ p5) → ((((p2 ∨ (False ∧ False)) → ((p2 → p3) ∧ p4)) → (p2 ∨ (p1 ∨ p4))) → p2))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20818749364973979097692647172 : (((((False ∨ p2) → ((((True ∧ p1) ∨ True) ∨ False) ∧ False)) → p2) ∨ (((((False → p4) → p2) ∧ p3) ∨ ((p2 → p2) → True)) → True)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54133273198335583080492247143 : (((p3 ∨ ((True ∧ (True → (p5 ∧ p4))) ∨ (p1 → True))) → ((p3 ∧ (((p2 ∧ (p4 ∧ (p4 ∧ p1))) ∨ p5) ∧ True)) ∧ (p5 → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234896277854599008567044992832 : ((True ∧ True) ∧ (((((p5 ∧ (p5 → p3)) ∧ p1) ∧ (((p2 ∧ (p2 ∨ ((p5 → p2) → p2))) ∧ p2) → ((True ∨ p4) → False))) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697905038446798674306778462485 : ((((((False ∧ (p3 → (p1 ∨ False))) → ((True ∨ p4) ∧ p3)) ∧ False) ∨ (p2 → ((p2 → (p5 ∧ (False ∧ (p3 ∨ (False ∧ p3))))) ∨ p2))) ∨ p5) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45533388666165854066817919883 : (((p1 ∨ (False ∨ (((((p2 ∨ p2) → ((True ∨ ((((True → p5) ∧ p2) → p5) ∨ p4)) ∧ p5)) ∧ (p5 ∨ p1)) ∨ p4) ∧ p5))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65469811829430613744343072001 : ((p3 ∨ (False ∧ ((p4 ∨ (False ∨ ((p3 ∨ ((((p1 ∨ False) ∨ (p4 → (p5 → True))) ∨ (p2 → (p2 ∧ p1))) ∧ p1)) → p2))) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227757702301178001600655986860 : ((p1 ∧ (p4 ∨ p3)) ∨ ((((p5 ∧ p1) ∨ p2) ∧ ((p5 ∧ ((p2 → p5) → p1)) ∨ p3)) → (p4 ∨ ((p1 ∨ (p4 → p4)) → (p5 ∨ True))))) := by
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
    cases h3
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h16 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h23 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765606102255297171611923442150 : (((p4 ∧ ((((p1 ∧ True) ∧ (((p5 → (p1 ∨ False)) → p4) ∧ (p4 ∨ True))) ∧ p4) → (p2 ∧ ((p5 ∧ ((False ∨ p4) ∨ p2)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319097076942204224832069945670 : (p4 ∨ ((((p4 → False) ∨ True) ∧ ((((p4 ∧ True) ∨ True) ∨ (p5 → p4)) ∧ (False ∨ ((False → True) → False)))) → ((p1 ∧ (p1 ∧ p2)) ∨ p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h11 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h13 : p4 := by
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h14 := h4 h13
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h16 =>
          -- False on the left can always be used.
          apply False.elim h16
        case inr h17 =>
          -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
          have h18 : (False → True) := by
            -- Implications on the right can always be decomposed.
            intro h19
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h17, we can now drive its conclusion.
          let h20 := h17 h18
          -- False on the left can always be used.
          apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h22 =>
        -- False on the left can always be used.
        apply False.elim h22
      case inr h23 =>
        -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
        have h24 : (False → True) := by
          -- Implications on the right can always be decomposed.
          intro h25
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h23, we can now drive its conclusion.
        let h26 := h23 h24
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h34 =>
          -- False on the left can always be used.
          apply False.elim h34
        case inr h35 =>
          -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
          have h36 : (False → True) := by
            -- Implications on the right can always be decomposed.
            intro h37
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h35, we can now drive its conclusion.
          let h38 := h35 h36
          -- False on the left can always be used.
          apply False.elim h38
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h40 =>
          -- False on the left can always be used.
          apply False.elim h40
        case inr h41 =>
          -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
          have h42 : (False → True) := by
            -- Implications on the right can always be decomposed.
            intro h43
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h41, we can now drive its conclusion.
          let h44 := h41 h42
          -- False on the left can always be used.
          apply False.elim h44
    case inr h45 =>
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h46 =>
        -- False on the left can always be used.
        apply False.elim h46
      case inr h47 =>
        -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
        have h48 : (False → True) := by
          -- Implications on the right can always be decomposed.
          intro h49
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h47, we can now drive its conclusion.
        let h50 := h47 h48
        -- False on the left can always be used.
        apply False.elim h50



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184855768154926483657034973217 : ((((p4 ∨ p1) ∧ False) ∧ (p3 ∨ (((p5 → p1) ∨ p5) ∨ True))) ∨ (p4 ∨ (((p2 ∧ (((p3 ∨ p3) ∧ (True ∨ p5)) ∧ p1)) ∧ p5) → p5))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h14 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_743375515864201866253089413155 : ((((p5 → p1) ∨ (p4 ∨ (p5 ∨ ((((p2 ∨ (p1 ∧ p2)) ∧ p4) → (False ∧ ((True ∧ p3) → p2))) ∨ ((p1 ∧ (p4 → False)) ∧ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262725260190894146324686253430 : (True ∧ (((p2 → (p5 → (((p5 ∧ (p1 ∧ p3)) ∨ ((p1 ∧ p4) ∧ p3)) → p3))) → ((False → (False → (p4 ∨ (p3 ∧ True)))) ∧ p1)) → p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → (p5 → (((p5 ∧ (p1 ∧ p3)) ∨ ((p1 ∧ p4) ∧ p3)) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h13
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h16 := h1 h2
  -- We need to get the right conjuct of h16 based on <expert-advice>.
  let h17 := h16.right
  -- One of the premise coincides with the conclusion.
  exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154910566975220253116232300588 : (((((((False → p2) ∧ True) ∨ (((p3 → p2) ∨ p3) → p4)) ∨ p4) → p5) ∨ ((False → True) ∨ True)) ∧ ((p2 → True) ∧ ((p4 ∧ p5) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65075487768754591816800380926 : ((p2 ∨ (p5 ∧ ((True ∨ p5) ∧ (p3 ∨ ((True ∧ p3) ∧ ((p3 ∨ True) → (((False ∨ (p1 ∧ (p3 ∨ (True ∨ p2)))) ∧ p1) ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777328559535156386774072046298 : (((p1 ∨ (((((p5 ∧ ((((((p2 ∧ p2) → False) → p2) → p1) ∨ p4) ∨ False)) ∨ False) ∨ p5) ∨ True) ∨ (p1 → (False → (p3 → p1))))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341010621777458990050007850081 : (p2 → ((p1 ∧ ((False ∨ p4) ∨ ((((((False ∧ p5) → p4) → p1) ∨ ((p5 ∨ (p5 ∧ True)) → p4)) → ((p1 ∧ p5) ∨ True)) ∨ p2))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137775329048133369592458147419 : ((p2 ∨ (((True ∨ (True → (p1 ∨ (p1 ∨ p4)))) ∨ True) ∧ (((p5 ∨ (((True ∧ False) ∨ p5) ∨ False)) ∧ True) ∧ True))) ∨ ((False → p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122333578718876497040840811774 : (((p5 → (p1 ∧ (True ∧ ((p2 ∨ True) → ((((p1 → ((p3 ∧ False) ∧ p1)) ∧ p2) → False) ∧ (p4 → p4)))))) ∧ (p3 → p3)) → (p3 ∨ True)) := by
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
theorem thm_5_vars_206116179960616330211292390833 : ((p4 ∧ (((False ∨ p4) → p3) → False)) ∨ ((p4 → (p3 → ((p2 ∧ ((p2 → p3) ∨ ((p1 ∧ (True ∨ p2)) ∧ p4))) → (p4 ∧ p2)))) ∨ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
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
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the left can always be decomposed.
  let h14 := h3.left
  let h15 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h23 =>
      -- One of the premise coincides with the conclusion.
      exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182927051221434415951149362642 : (((p3 ∨ (p5 ∧ p5)) → (p4 → (((p5 ∧ p2) ∨ p2) ∨ True))) ∧ ((p3 → (((((p4 ∨ p2) ∨ p5) ∧ p1) ∧ (p4 ∧ p3)) ∨ p3)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61941393719604630326856473076 : ((p2 ∧ ((p5 ∧ (True → (p5 → (((p1 ∨ (((p5 → False) ∧ p5) ∧ p2)) ∧ p2) ∧ p5)))) ∧ (p1 ∧ (((p1 → p2) → p4) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50238204708921389762591756114 : ((((((False ∧ (True ∨ ((p4 ∧ (p1 ∨ False)) → (False ∧ True)))) ∧ (p1 ∧ (p4 ∧ False))) → p1) → p1) ∨ ((True ∨ (p4 → p5)) ∨ p3)) ∨ p4) := by
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
theorem thm_5_vars_118595247028889517790278031689 : ((p4 ∨ (((False ∧ (False ∧ p5)) ∧ (p3 ∧ (((((p3 ∨ True) → p1) ∨ p3) ∧ (p2 ∧ p3)) ∧ (True ∨ p4)))) ∧ (p4 ∨ p4))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134951304993773258255477131605 : (((((((((p1 → p4) ∨ p1) ∧ ((p1 → p3) → p1)) ∨ p2) ∧ p5) ∨ p1) → (p1 ∨ (p4 ∧ p2))) ∧ (False → True)) ∨ ((True → p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797411023037500398972646169220 : (((p1 → ((True ∧ ((True → (p2 → (p5 ∨ ((p1 → p5) ∧ ((p5 → p5) ∨ (True ∨ True)))))) → ((True ∨ p2) ∧ (p3 ∨ p3)))) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115812756935884263341352719075 : ((((p3 → (p4 ∧ p2)) → p1) ∧ (((True ∧ ((p4 ∧ p4) ∧ p5)) ∨ (False ∧ ((p2 → p3) ∨ (p1 ∨ True)))) ∨ (p4 ∨ p1))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40437978728923610759411991543 : (((((True → ((((p2 → (p4 ∨ p3)) ∧ p2) ∨ p3) ∧ False)) → ((True → (p5 → (p3 ∨ p3))) ∧ ((p3 ∧ p1) → p1))) ∨ False) ∨ p3) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111880962021291722142781080214 : (((((p4 ∨ True) → ((p1 ∨ (((True → p1) ∨ p3) → (p2 → (p3 ∧ p4)))) ∧ p4)) → ((p1 ∨ (p1 ∧ p5)) ∨ p4)) ∨ p4) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735396031511912268757016011947 : ((((p4 ∨ p2) ∧ ((False ∨ ((((p5 ∨ (p4 ∧ ((((p4 ∧ p5) → p3) ∧ (p2 → True)) ∧ p1))) → p5) ∧ (p3 ∨ True)) → p2)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47211570020335237726363395590 : ((((((False ∨ (p3 → True)) ∨ ((p1 ∨ False) ∧ p2)) → p2) ∨ (((p2 ∧ p4) ∨ False) ∧ (((True → p1) ∧ p4) ∨ True))) ∨ (p4 → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134128447952860330802025824122 : ((((p5 → (((p1 ∨ (p3 ∨ ((p5 → p5) → (True → False)))) ∧ ((True → p2) ∨ p2)) ∨ p1)) ∨ (p3 ∧ False)) ∨ True) ∨ (p4 ∨ (True ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185272676765116348193731731904 : ((p1 ∧ (True → (True ∧ (((p2 ∨ p3) ∨ (p1 ∧ p1)) ∧ True)))) ∨ (p2 ∨ ((((p5 ∨ p5) → p5) → ((p5 ∨ (p3 ∧ p5)) ∧ p1)) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ p5) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718294011673551760892560937283 : ((((((True ∨ p2) ∧ p1) → p3) ∨ ((((p5 → ((((((True ∨ p5) → p4) ∧ p5) ∨ p5) → p5) ∨ False)) → p4) ∨ p2) ∧ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166011444587975403037769041485 : (((p1 ∨ p5) ∨ (((True ∨ p1) ∧ (((False ∧ p1) ∨ p4) ∧ ((p4 → p4) → p2))) ∨ p5)) ∨ ((False → True) ∨ (((p2 ∨ p2) ∧ p2) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204365059438459829386160936819 : (((p2 ∨ (p4 ∨ (p3 ∨ p4))) ∧ p2) ∨ ((p5 → ((False ∧ ((p5 → (p3 ∧ p5)) → False)) ∧ (((p2 → (True ∧ p4)) ∨ p2) ∧ p1))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185309862716394502933842054741 : ((p3 ∧ ((((p2 ∧ p4) ∨ (p5 → False)) ∧ (p5 → p2)) ∨ p1)) ∨ ((False → p1) → (((p2 ∧ (p1 → (p4 ∧ (False ∧ p3)))) → p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329320688195620354589089962613 : (True → ((p5 → (False ∨ p2)) ∨ (((p3 → (((True → ((((p4 → False) ∧ p3) ∧ p1) → False)) → (True → p1)) ∨ (p5 ∨ p2))) ∨ p1) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206154565562226350615055737388 : ((p5 ∧ (((False ∨ False) ∧ p2) ∨ False)) ∨ (((p2 ∨ False) ∧ (p3 ∧ (((((False → (False → (p3 ∨ False))) ∧ p1) ∧ p2) → p2) ∧ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750625258611074452614591664774 : (((True ∧ ((p3 ∧ (p5 ∨ ((((False → p1) → (p1 ∨ False)) → (True ∨ (False → p3))) ∧ p5))) ∧ (False ∧ ((p5 → (p5 ∧ p4)) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57148485083589109656211302705 : ((((p5 → False) ∧ False) ∨ ((p3 → ((p5 ∧ p2) ∨ ((((p5 ∧ (p4 → ((p4 ∨ (p4 ∨ True)) → True))) → False) ∧ p1) ∧ False))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262108029677207994638598777586 : (True ∧ (((((p1 ∧ (True ∨ (p2 ∧ (p1 → (p2 ∧ ((True ∧ (p3 ∧ False)) ∨ (True → (p4 → p4)))))))) → p4) ∧ (p4 ∨ p5)) ∧ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41935411578655190758942168620 : ((((p2 → (p2 ∧ p3)) → ((p2 ∨ (True ∨ (p3 → (False ∧ ((False ∨ p3) ∨ (True → p5)))))) → ((p5 → True) → (p5 ∧ False)))) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148034700217685079211336508387 : ((((p5 ∧ p2) ∧ (False ∧ (((p2 ∧ p1) ∧ ((p4 ∨ p1) ∧ (p2 ∧ (False ∨ False)))) ∨ p4))) ∨ (p3 ∨ p4)) ∨ ((p5 → p5) ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51497185489946606229109035809 : (((((p2 ∧ True) ∨ p2) ∧ (p2 ∧ (((p2 ∨ p5) ∨ (False ∨ (p1 ∨ False))) ∨ (True ∨ p1)))) → (p1 ∨ (p1 ∨ (p2 ∧ (False → False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328291032086448850297802935246 : (True → (((p4 ∧ (p5 ∨ (p4 → ((p1 → (True ∧ p3)) → False)))) ∨ ((((True → p3) ∧ True) ∧ True) ∨ True)) ∨ ((p3 ∨ (False ∨ p5)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174800197485350917725740625879 : (((True → False) ∧ ((p4 ∨ (((False ∧ ((p1 → p3) ∨ True)) ∧ True) ∨ True)) ∧ p4)) → ((((p5 ∧ p4) ∨ (p1 → p5)) ∧ p5) ∧ (p2 → True))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h7
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    case inr h15 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h17 := h2 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h22 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h24 := h18 h23
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h29 := h27.left
      let h30 := h27.right
      -- False on the left can always be used.
      apply False.elim h29
    case inr h31 =>
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h33 := h18 h32
      -- False on the left can always be used.
      apply False.elim h33
  -- Implications on the right can always be decomposed.
  intro h34
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357274954768007425716014532846 : (p5 → ((p4 ∧ p2) ∨ (((p5 → ((p4 ∧ ((p5 → p3) → (p4 → (p3 ∨ ((p3 ∧ p1) ∧ p2))))) ∨ p1)) ∨ True) ∨ (True ∨ (p3 ∨ p5))))) := by
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
theorem thm_5_vars_180377713593672575037231564810 : ((((p3 ∨ ((p1 ∨ True) → p3)) ∧ (p3 → (p1 ∧ p5))) ∨ (p4 ∧ p4)) → ((p3 ∧ ((((p4 ∨ p3) ∧ p5) ∨ p1) ∨ False)) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46967038947251583153313501681 : (((((p4 ∧ ((((p4 → ((True ∧ (((p3 ∨ p1) ∧ p2) → p5)) → False)) ∨ True) → (p1 ∨ p4)) ∧ p4)) ∨ p3) → p2) ∨ (p1 → p1)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788421520853786530347784020944 : (((p5 ∨ (((((p3 → p1) ∧ p3) ∧ (((p1 ∧ p3) ∧ p2) → p5)) ∨ (((False ∧ True) ∨ ((True ∧ (p3 ∨ p1)) → True)) ∨ False)) ∨ p5)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_319462868283990321042740162323 : (p4 ∨ (((False ∨ p2) ∧ ((p3 ∨ p2) → ((p4 ∧ (False ∨ p5)) → p4))) ∨ (((((p1 ∧ p1) → (p1 ∨ p3)) ∨ p5) → (p3 ∧ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133594261251759314375570256671 : ((((p1 → ((p4 ∨ (p3 ∧ ((((True ∧ p2) ∧ p3) → (p5 → ((p3 ∨ p1) ∨ p2))) → False))) ∧ p5)) ∨ p1) ∧ p4) ∨ ((False ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309387382775143387487539111807 : (p2 ∨ ((p3 ∧ (((True ∨ ((p1 → p1) ∨ p1)) ∨ (((p1 ∨ (False ∧ p5)) ∧ (p3 ∨ p2)) ∨ (p4 ∨ p3))) → (False ∧ p3))) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105703974647368793443246858877 : ((((False ∧ ((p4 ∧ (p5 ∧ ((p1 ∨ (False ∧ p3)) ∨ (False ∧ p2)))) ∧ False)) ∨ True) ∨ ((False → (p3 → False)) ∧ (p5 → True))) ∧ (True ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119785920795111780066503320020 : ((((((p5 ∧ ((((p3 ∧ p1) → ((False ∨ (False ∨ p1)) ∨ p3)) ∨ (p3 → True)) ∨ (p2 → p3))) ∨ True) ∨ p1) → False) ∧ p3) → (False ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p5 ∧ ((((p3 ∧ p1) → ((False ∨ (False ∨ p1)) ∨ p3)) ∨ (p3 → True)) ∨ (p2 → p3))) ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809349107540676517217572486415 : (((p5 → ((p1 ∨ (p5 → ((((p1 ∧ False) ∨ (p4 → p3)) ∨ ((p3 → (((False ∨ p1) ∧ (p3 → p5)) → False)) ∨ p1)) ∨ p5))) ∨ p3)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37361098996387181474955401549 : (((((((p1 ∧ p2) ∨ ((p2 ∧ False) ∨ p4)) ∨ ((p2 ∨ (True → False)) ∧ ((False ∧ True) ∧ ((True ∧ p2) → p5)))) ∨ True) ∨ False) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314667321713188464353741992722 : (p3 ∨ ((True → (((p5 ∧ (p5 → False)) ∧ (p5 ∨ (p4 ∧ p4))) ∧ (p4 → (p5 ∧ p2)))) ∨ (True ∨ (((p3 ∧ (p5 ∧ p1)) ∨ False) → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251892922540533073710313083842 : ((p3 → p5) ∨ (p4 → ((((True → p5) ∧ (p2 ∧ ((p1 ∧ (p2 ∧ p1)) ∨ False))) ∧ p4) ∨ ((True → (p5 ∧ (p2 ∨ (False → p3)))) ∨ True)))) := by
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
theorem thm_5_vars_61892580820019208383545761438 : ((p2 ∧ ((False ∧ (True ∧ (((((p1 ∨ True) ∧ p5) ∧ p3) → (p1 → p5)) → ((p3 ∨ ((False ∧ p4) → p5)) → p2)))) ∨ (p2 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719473190317846211808750529326 : ((((p1 ∨ (p4 → (p3 ∧ p1))) ∨ (((True → p1) ∧ ((p2 ∨ False) ∧ (((p4 → p5) → True) ∧ (p2 ∧ ((p4 → p3) ∨ False))))) → p1)) ∨ p2) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355420607279502133353011663852 : (p5 → (((((False ∨ (p3 → p2)) → (p5 → ((p4 → ((((p4 → p1) ∧ p1) ∨ (p4 ∨ p3)) ∨ p4)) ∧ p4))) ∨ p3) ∨ p5) ∧ (p5 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180011285231158112275154885120 : ((((p3 → True) ∨ (p1 ∧ (((p2 ∨ (p2 ∧ True)) → False) ∧ p2))) ∨ False) → (((False → False) → (p3 ∧ (((p5 ∧ p4) → p2) ∧ p1))) ∨ True)) := by
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
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65580758233409943100705345301 : ((p3 ∨ (p5 → (True → (((((p5 ∧ ((p5 ∨ p1) ∧ p2)) ∨ (p1 → (p3 ∧ ((False → (True → p3)) → p3)))) ∨ True) ∨ p5) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352480827354090858122917488858 : (p4 → ((p5 ∧ (p4 → p1)) → ((((p1 ∨ (False → p5)) → (p4 ∧ (p4 → p2))) ∨ (False ∨ p4)) ∨ (p4 → (True ∧ (p5 → (p5 → p5))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154770182239781092452079760827 : (((p3 ∨ ((((p1 → ((p3 ∧ ((p1 ∨ False) ∨ False)) → True)) ∨ p3) ∨ p1) ∨ p3)) ∨ (p4 ∧ False)) ∧ ((p4 ∧ (False ∧ p2)) ∨ (p4 ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191845567235028425504152593534 : ((p3 ∨ (False ∧ (((p5 ∧ (False → p2)) ∨ p5) ∨ False))) ∨ (((True ∧ ((p2 ∨ p4) ∧ True)) ∧ ((p2 ∧ p2) ∧ (True ∧ (p5 ∧ p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141095088932924372736436740843 : ((((True ∧ (p5 ∨ (True → (False ∧ True)))) ∨ p5) → (True → (p1 ∧ ((p5 ∨ ((p1 ∧ (p1 → p2)) ∧ p5)) → False)))) → ((p3 ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51186334037050156014941527606 : ((((p4 ∨ ((((p1 → (p5 ∨ (p1 ∨ p4))) → p3) ∨ p2) → False)) ∧ ((p1 → p1) ∨ p3)) ∨ (p5 ∨ ((p5 ∨ (p5 → p4)) → True))) ∨ p4) := by
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
theorem thm_5_vars_136377201942334149603156459109 : ((((p3 → (True → p1)) → p3) ∨ (((((True ∨ True) ∧ True) → p3) → (p5 ∧ p5)) ∨ (p1 → (p4 → (True → p3))))) ∨ ((False ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313983657391413908412611530645 : (p3 ∨ (((p2 ∧ (p2 ∧ ((p1 ∨ True) ∧ p3))) ∨ (p4 → (False → ((((p1 ∨ (p2 ∨ p3)) ∨ False) → p1) → (p5 ∨ p5))))) ∨ (p4 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611061157638723610953062519395 : (((((((p5 → (False ∧ p1)) ∧ p5) ∧ (p2 ∧ ((p2 ∨ True) ∨ ((((False ∨ p4) ∨ (p1 → False)) ∨ False) ∨ (p5 ∨ p5))))) → p4) ∨ p4) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h10 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h11 := h4 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h14 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h15 := h4 h14
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h22
        case inr h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h25 := h4 h24
          -- We need to get the left conjuct of h25 based on <expert-advice>.
          let h26 := h25.left
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h30 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h31 := h4 h30
        -- We need to get the left conjuct of h31 based on <expert-advice>.
        let h32 := h31.left
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h34 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h35 := h4 h34
        -- We need to get the left conjuct of h35 based on <expert-advice>.
        let h36 := h35.left
        -- False on the left can always be used.
        apply False.elim h36
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48668782434463923247349506189 : (((((((False ∧ p5) → p3) ∧ (((p2 ∨ False) ∨ p5) ∧ p1)) → p5) → (((p1 ∧ (p3 ∨ True)) ∧ p5) ∨ True)) ∧ (p3 ∨ (True ∨ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_649619891498990210055298565741 : ((((((((p2 → (p3 → False)) ∨ (p4 → p4)) ∧ (p4 ∧ True)) ∨ (((p3 → (p5 ∨ p2)) ∨ p1) ∧ p3)) ∨ (True ∨ p2)) ∧ (p1 → p1)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608317621968359280696615945377 : (((((((((p2 ∧ p5) ∨ ((p4 ∧ p1) → p4)) → p1) → (p5 → (((False → p5) ∨ (p1 → p5)) ∧ (p2 ∨ False)))) ∨ p4) ∨ True) ∨ False) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_112771471019436999763430743579 : ((((False → ((((False ∨ (p4 ∧ True)) ∨ p1) ∧ p2) → True)) → ((p4 ∨ p1) → (((p3 → p1) → p4) ∧ (False → True)))) → p5) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118611285111800332224127006777 : ((p4 ∨ (((((p2 ∧ (p3 ∧ False)) ∨ p4) ∨ p3) ∧ (((p5 ∧ False) ∨ p4) ∨ (p3 ∧ p1))) → (((p1 → False) ∧ p1) ∧ p3))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65428421569362533867412398984 : ((p3 ∨ ((p1 ∨ (p1 ∨ p3)) → (p2 → (((True → p2) → ((p5 → ((p3 ∨ True) ∧ (p2 ∧ p1))) ∨ True)) ∧ ((p4 → p2) ∨ p4))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h14
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51991490602876349830699174410 : ((((p1 ∨ True) → (((p3 ∧ p1) ∨ ((p2 → (False ∨ p1)) → (True → p3))) ∧ True)) ∨ ((p1 ∨ True) ∧ (False ∨ ((p1 ∨ False) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115289120987671422368310342970 : (((((True → (p1 ∨ p3)) → (True → (False ∨ p5))) ∧ p3) → (((p2 ∨ False) ∨ (False → ((p3 → p2) ∨ False))) → (p4 ∨ p5))) ∨ (p4 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h1.left
      let h6 := h1.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (True → (p1 ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h7
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (True → (p1 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h20 := h16 h18
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h21 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h22 := h20 h21
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736338523996723378279129514185 : ((((False → p5) ∧ (((((p2 ∧ (False → (p3 → (p1 → p4)))) ∧ (True ∧ p4)) ∧ ((((True ∧ True) → p5) ∨ p3) → p5)) → p4) ∨ p4)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h6.left
  let h10 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301944201877478205216161791658 : (False ∨ ((p2 ∨ p1) → (p5 ∨ (((((p4 ∧ p2) ∧ (((p1 ∧ p3) ∧ False) ∨ p3)) ∨ True) ∨ ((p2 ∨ False) ∨ ((p1 ∧ p5) → False))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
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
theorem thm_5_vars_184776458665802149839645643873 : ((((False → (p1 ∨ p2)) ∧ p3) ∨ (((p1 → p2) ∧ p1) ∨ False)) ∨ ((((p1 → p1) ∨ (((p4 → p5) ∧ p3) ∧ (p3 ∧ p5))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138367049633538465958250858858 : ((p4 → ((((p5 → False) → p5) ∨ (p5 → (True → (p3 ∨ (p3 ∨ True))))) ∧ (True → ((False ∨ (p2 → p1)) ∨ p1)))) ∨ (p3 ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251353534187622081687185322854 : ((p2 → p4) ∨ (((((True ∧ p4) → p2) → ((False ∨ p2) ∧ ((False → p2) → (((False ∧ (p1 → (p2 ∧ p4))) → p5) → p3)))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629033084943416609955887142251 : ((((((p4 ∨ ((p4 ∧ (p4 → (p4 → (p4 → ((((((p5 ∧ True) → False) → p1) ∨ False) ∧ p5) → p3))))) → p4)) ∧ p3) ∨ p2) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166223591339000945872210995248 : ((p2 ∧ ((((p4 ∨ (p3 → (p4 ∨ p3))) ∧ (p4 → p5)) → p2) ∧ ((p1 ∨ p1) ∧ p5))) ∨ (p5 → (((p3 ∧ (p2 ∧ p3)) ∧ p5) → p5))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147305082077276641798512957825 : ((((((p5 ∨ ((False ∨ False) ∨ (p2 → p4))) ∧ p3) ∨ ((((p2 ∨ True) ∧ p5) → False) ∨ p5)) → p2) ∨ False) ∨ ((p4 → p4) ∨ (True ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310129802123574338473555672194 : (p2 ∨ (((p5 → p3) ∨ (p5 ∧ (p2 ∧ (((p3 → p5) ∨ p1) → (p4 → p5))))) ∨ ((False ∧ p5) → (p5 ∨ ((False → (p4 ∧ p2)) ∧ p5))))) := by
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



