variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226291826143514823578575272119 : (((p4 ∨ p2) ∨ p5) ∨ ((p3 ∧ p2) ∨ ((((p4 ∨ (((p5 ∧ (((p2 ∨ False) ∧ p3) ∧ True)) → False) ∧ (p1 ∨ False))) ∨ p4) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_184034474641931468675703450290 : (((((p3 ∨ (p1 ∧ p2)) → (p3 ∧ (p5 ∧ p2))) → p3) ∨ True) ∨ (True → ((p4 → (((p4 ∧ (p2 ∨ p3)) → p5) ∧ (p3 ∨ p4))) → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734736728784928352801384781806 : ((((p2 ∨ True) ∧ ((((True → (False ∨ (False ∨ p3))) ∨ p4) → (p3 ∨ ((p4 ∨ (p2 → p3)) ∧ p4))) ∨ (p3 ∨ (False ∨ (p2 → p3))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41494077604609296601679029226 : ((((((p3 ∧ (p2 ∧ p3)) → (p4 ∨ (p4 ∨ (False ∧ p1)))) → p3) → ((((((p4 ∧ p4) ∧ p3) ∨ False) ∨ False) ∨ p3) ∧ False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228559343033685750877426044342 : ((p1 ∨ (False ∨ False)) ∨ (((((p4 ∧ (((p1 → p2) → (False ∨ p4)) → p3)) ∧ False) ∧ (True ∧ False)) ∧ True) ∨ (False → ((p1 ∧ p5) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134264737155630353567921842580 : ((((p3 ∧ (p3 ∨ p4)) → ((p2 ∧ ((False → True) ∧ ((p2 ∧ p4) ∨ p3))) → (False ∧ (p4 ∧ (p2 ∧ p2))))) ∨ True) ∨ ((p3 ∨ p1) ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788114581044564103035238635760 : (((p5 ∨ (((p4 ∧ (((p2 ∨ (p3 → ((p1 ∨ p5) ∧ p5))) ∨ p4) ∧ ((False ∨ p3) → (p1 → p2)))) ∨ (p5 ∧ (p3 ∨ True))) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200436073006902768030383636055 : (((p4 ∨ True) ∨ (((p3 ∨ True) ∧ p3) ∨ False)) → ((((p3 ∨ True) → False) ∨ ((p2 ∧ (False ∨ ((p2 ∨ (True → p3)) ∨ p3))) ∧ False)) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h6 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h7 := h3 h6
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : (p3 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h10 := h3 h9
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h15 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h16 : (p3 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h17 := h3 h16
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h19 : (p3 ∨ True) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h20 := h3 h19
          -- False on the left can always be used.
          apply False.elim h20
      case inr h21 =>
        -- False on the left can always be used.
        apply False.elim h21
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Conjunctions on the left can always be decomposed.
    let h25 := h23.left
    let h26 := h23.right
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h24
        case inr h31 =>
          -- False on the left can always be used.
          apply False.elim h24
      case inr h32 =>
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307728199635322770191161541089 : (p1 ∨ (p3 → (((((False → ((False → ((p2 → p3) ∨ p4)) → True)) ∧ p2) → p5) ∨ ((p2 ∨ p2) → ((True → p5) ∧ (p2 ∧ p1)))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180320421136227494714528151075 : (((((p1 ∨ p3) → True) ∨ (p1 ∧ ((p5 ∨ p4) ∧ p1))) ∧ (p5 → False)) → ((((p5 ∨ p5) ∧ False) ∨ ((p4 ∧ p4) ∨ (False ∧ False))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179782132902338826641688808929 : (((((p4 → p2) ∨ p1) ∧ ((p5 ∨ True) ∨ ((False ∨ p5) ∧ False))) ∧ p5) → ((p1 ∧ (p1 ∧ p2)) ∨ (((p3 ∨ p1) → (False ∨ True)) ∧ p5))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h9
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
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h13
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
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h18
  case inr h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h24
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h28
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
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h31 =>
      -- Conjunctions on the left can always be decomposed.
      let h32 := h31.left
      let h33 := h31.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h34 =>
        -- False on the left can always be used.
        apply False.elim h34
      case inr h35 =>
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49801099139623227492906770975 : (((True → ((((False ∧ p3) ∨ ((True → True) ∨ True)) → p4) ∧ (((((p1 ∧ True) ∧ p2) ∨ p2) ∨ p1) ∨ p3))) → ((p3 ∨ p2) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788350722503754213091368481226 : (((p5 ∨ ((((p3 → (p1 ∧ False)) ∧ (True → ((p4 ∧ (p3 ∧ ((p5 → p1) → (p1 → (p5 ∧ (p4 ∧ True)))))) ∧ p3))) → p5) ∨ p2)) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h7
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201124518109767677791831375621 : ((True → (p4 ∨ (((p3 ∨ p3) → p4) ∨ p2))) → ((p4 → p4) → (((((((True ∧ p5) ∧ p3) ∧ (p5 → p2)) → p1) → True) → False) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((True ∧ p5) ∧ p3) ∧ (p5 → p2)) → p1) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213575324039389359378072877401 : ((((p4 ∨ False) ∧ p1) ∨ p1) ∨ (p5 ∨ (((False ∨ p3) ∧ (((p4 ∨ (p2 ∨ (p2 ∧ p2))) → p4) ∧ ((p1 → p1) → True))) ∨ (True → True)))) := by
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
theorem thm_5_vars_176769066176415254168970173313 : (((False ∨ (True ∨ p1)) ∨ (False ∨ (((p3 → (p3 ∧ p2)) → p5) ∨ False))) ∧ ((((p4 ∨ p1) → False) ∧ ((p1 ∨ True) → False)) ∨ (p2 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656665940027897065464704826530 : (((((((p2 ∨ p3) ∧ (p5 ∨ False)) ∧ p2) ∧ (((p1 ∧ p4) → ((p3 ∨ p2) → (p1 ∨ ((p2 ∨ True) → False)))) → p1)) ∨ (p2 ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2561897679482616043736527419 : ((False ∧ ((False → p5) → (False ∨ (False ∨ p4)))) ∨ (((p1 ∧ p4) → p4) → (True ∨ ((p2 → p3) ∧ (((p4 → False) → p5) ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197639925932848916620653352908 : ((((False → (p4 ∧ False)) ∨ True) → (p4 ∨ False)) ∨ ((True ∨ ((p3 → (p1 ∨ ((p5 ∧ ((p3 ∧ True) → (p5 → True))) → p5))) ∧ True)) ∧ True)) := by
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
theorem thm_5_vars_593188760251775342807609588215 : ((((((p1 → (p3 ∨ p2)) → ((True → (p5 ∨ p4)) ∧ (((p2 → (p1 → (True → p3))) ∨ True) ∧ p2))) ∨ (p2 ∧ (p1 ∨ p2))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152025057841704587724121815072 : ((((False ∨ ((p4 ∨ (p4 ∧ (p1 → p3))) → p2)) → True) ∧ (((False → (p5 ∧ True)) → p1) ∧ (False ∨ p5))) → ((p2 ∧ p1) ∨ (True → p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345525227854085595895619453322 : (p3 → ((((((False ∨ (p2 ∧ True)) ∧ p5) → p4) ∨ (True ∧ False)) ∧ ((p3 → (p5 → p1)) → (((p3 ∨ p2) → p2) ∨ (p5 ∨ p3)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153323047126943424354773915843 : ((p1 ∨ (p1 ∨ ((p4 ∧ (True ∨ (p2 ∧ (p3 ∧ (True ∧ p4))))) → (False ∧ (False ∧ ((p3 → p1) ∧ p5)))))) → (p1 → ((p4 ∧ p4) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18123019084938804248659825973 : (((p3 → ((False ∨ (((p1 → (p3 → p2)) ∨ False) ∧ (p1 → False))) ∧ (False ∧ (True ∧ (p1 ∧ p3))))) ∨ (((p5 → True) ∨ p4) → True)) ∧ True) := by
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
theorem thm_5_vars_149431741631131605642497677491 : ((True ∧ (p2 ∨ (True → ((((p4 ∧ ((p1 ∨ p5) → False)) → p4) ∧ ((p2 ∧ p3) → (p1 ∨ False))) ∨ p5)))) ∨ (True ∨ ((True → p5) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303209145554002170992467728734 : (False ∨ (p4 → (p1 ∨ ((((p3 ∧ p5) ∧ p4) ∧ False) ∨ (True ∨ ((p1 ∧ (p3 ∨ p1)) ∨ ((((p3 ∧ p4) ∧ p1) ∧ (p5 ∧ p3)) → p5))))))) := by
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
theorem thm_5_vars_777559418820232188428712054113 : (((p1 ∨ (((p4 ∧ ((False → p4) → (False → (True ∧ True)))) → (p4 ∧ False)) ∨ (True ∨ ((((p4 → False) → p2) → False) ∨ (p1 ∨ p5))))) ∨ p3) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314844889634306666209435350057 : (p3 ∨ ((p5 ∧ (((p2 ∨ (p3 ∨ (p2 ∨ p2))) → (p5 ∨ p1)) ∧ p4)) ∨ (((False → (p5 → p5)) ∧ ((True → (p5 ∨ True)) ∨ p2)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60279033232127683670875700074 : (((False → p5) → ((True ∨ (((False ∨ p5) → (p3 → (((((p4 ∨ p1) ∧ (True ∨ (p5 → True))) ∨ p1) ∨ p1) → p2))) ∨ p4)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621784044853722233178994344361 : ((((p1 ∧ ((p2 ∨ (p2 → (((False → ((p1 → p2) ∧ (p2 → (p4 ∨ ((p1 ∧ p2) ∨ (False ∧ p2)))))) ∧ p4) ∧ p4))) → p2)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115445989607546886154915786789 : (((((p3 ∧ p2) ∨ p2) ∧ (p4 ∨ (p1 → p1))) ∨ (p1 → (((p5 ∨ True) ∧ p4) ∧ ((p3 ∨ ((True ∨ p1) → p4)) ∨ p5)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317839548014938474121047144344 : (p4 ∨ (((p2 ∨ (p5 → p4)) ∨ (p1 → ((p3 → p3) ∧ (p3 ∧ (p5 → ((p1 ∨ False) → ((True → p2) ∧ ((False ∨ False) → p1)))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738180201451418679556784282248 : ((((False ∧ p2) ∨ (p5 ∨ (p1 ∧ (((p2 ∨ ((p3 ∧ (p3 ∨ p1)) → p5)) ∧ p4) ∧ ((((p4 ∨ (False ∨ p4)) ∨ True) → p4) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308597347664369422000907171844 : (p2 ∨ ((((p5 ∧ p4) → False) → (((p2 ∨ p3) ∧ (p3 ∧ (((((p2 ∧ False) ∧ p5) ∨ p4) → True) → False))) → (p5 ∨ (p5 ∧ p1)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : ((((p2 ∧ False) ∧ p5) ∨ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h8
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h4.left
    let h13 := h4.right
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h14 : ((((p2 ∧ False) ∧ p5) ∨ p4) → True) := by
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h14
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110946727598962893773463309952 : ((((p5 ∨ (((((((False → (p1 ∨ (p2 ∧ (p3 ∨ p3)))) ∨ p2) ∨ p5) ∨ p3) → p1) ∨ False) ∧ p5)) ∧ (p5 ∧ True)) ∧ p1) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44083579881910961301022998696 : (((((p1 ∨ p4) ∧ (p2 ∧ (p5 ∧ (((((True ∨ p5) → True) ∨ True) → True) ∧ ((p3 ∧ p1) ∨ p1))))) ∧ (p5 → (p2 ∧ False))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229748579180174960287683352972 : ((p4 → (p1 ∨ p3)) ∨ (p1 ∨ ((p5 ∧ p5) ∨ (p5 ∨ (p1 → ((False ∧ ((p2 ∨ True) ∧ (True ∧ p4))) → (p1 ∧ ((p1 ∧ p2) ∧ p3)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h9 := h2.left
  let h10 := h2.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135732128165902540780381096129 : ((((((p3 → ((p4 ∨ p2) ∨ ((False → p1) ∨ p2))) ∨ p1) → p1) → p4) ∨ ((p3 → ((False ∧ p3) ∨ p3)) ∨ p1)) ∨ ((p4 → False) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299288365676318099165259949312 : (False ∨ ((((((False ∧ (p4 ∧ True)) → (True → (p3 → p5))) → p5) → p3) ∨ (((True → ((p3 ∧ (True ∧ True)) ∧ p4)) → p2) ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713957182912141654566067951670 : (((((False → ((True ∧ p4) → p4)) ∨ p4) → (((p1 → (False ∧ (False ∨ (((p2 ∨ (p1 → p1)) → (False ∨ p2)) → p2)))) → p2) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209168931667388225266603215001 : ((p3 ∨ (p5 ∨ (True ∨ (p5 → p1)))) → (True → (p3 → (True → ((p1 ∨ p2) ∨ (p5 → (False → (p1 ∨ ((p3 → (p2 → p4)) ∧ p4))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182018112779349066342307747045 : ((((p4 ∨ ((False → (p3 ∨ p3)) ∧ p2)) → (True ∧ False)) ∨ True) ∧ (((True ∧ p3) ∧ (False ∧ ((p4 → (p3 → p2)) → p1))) → (p5 → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h4.left
  let h8 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42973452987861026548556543198 : (((p5 → ((((p1 ∧ (p1 ∧ (((p5 ∨ ((p2 ∧ True) ∧ p5)) → (False → p3)) → True))) ∧ p1) ∨ p1) → (p5 → (p3 → False)))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192175741868073522318575847398 : (((((p5 ∨ ((p3 ∨ p2) → False)) ∧ p3) ∨ True) ∧ True) → (((p4 ∨ p4) ∨ ((p5 ∧ (p5 ∨ p2)) ∨ (True ∨ (True ∧ True)))) ∨ (p2 ∨ p2))) := by
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
    cases h5
    case inl h7 =>
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
    case inr h8 =>
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
  case inr h9 =>
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
theorem thm_5_vars_250163162718720074826457167853 : ((True → p5) ∨ ((((p1 ∧ p1) ∨ True) ∨ ((True ∧ p5) ∨ (p4 ∧ (p1 ∨ p3)))) → ((((p3 ∧ (p5 ∨ p3)) ∧ p1) ∨ p5) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h18 =>
          -- Conjunctions on the left can always be decomposed.
          let h19 := h18.left
          let h20 := h18.right
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
          case inr h22 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h19
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h24 =>
        -- Disjunctions on the left can always be decomposed.
        cases h24
        case inl h25 =>
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- Conjunctions on the left can always be decomposed.
          let h31 := h30.left
          let h32 := h30.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
          case inr h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h34
  case inr h38 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h39 =>
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h43 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h44
      case inl h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- Disjunctions on the left can always be decomposed.
        cases h50
        case inl h51 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h49
        case inr h52 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9101389749298161068264339451 : ((((p4 ∧ ((p2 → ((((p1 → p2) → p1) → p1) ∧ p4)) → p1)) ∧ ((((p1 → ((p1 ∧ p4) ∨ False)) → p1) ∧ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52191354345599793542563741843 : (((((p1 → p2) ∨ False) ∧ ((p5 ∧ (p2 ∧ p1)) ∨ (p2 ∧ (p2 → (p2 → p4))))) → (((p5 → p1) ∧ ((p2 → True) ∨ False)) ∨ p2)) ∨ p5) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318975306699321622166916933041 : (p4 ∨ ((p5 → ((((p4 → (((True → (p5 ∧ p4)) → p1) ∧ p2)) → False) ∨ (True ∨ (p2 ∧ (False ∨ p5)))) ∧ False)) → (p5 → (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353714953146550644706817471355 : (p4 → (True → (((p2 → ((True → False) ∧ ((p4 ∨ (p4 ∧ ((p4 ∨ p1) ∨ p1))) → (p5 ∧ (False ∨ (p2 ∨ True)))))) ∨ (p5 ∨ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56819640479114533499821249257 : ((((True → p3) → p3) ∧ ((((p4 ∨ ((True ∧ (False ∧ p3)) → (p3 ∧ (((p5 ∧ p5) ∨ p5) → p5)))) ∧ False) ∨ (p3 → p4)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46825280519217813529464632131 : (((((p3 ∧ (p2 → (((p5 → p3) ∨ p3) → (p3 ∨ ((p4 → (p5 ∨ p5)) → (p5 ∨ False)))))) ∨ (p5 ∨ p1)) ∧ p3) ∨ (p1 → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669785484501534949016960933904 : (((((((p1 → ((p4 ∧ (p2 → False)) → (False ∨ (p3 ∨ p5)))) ∧ p4) → p2) → (p3 ∨ (p1 ∧ (p5 → p2)))) ∨ ((p4 ∨ p1) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_66552655261790343989697618572 : ((True → (((p2 → (p3 → (True ∧ (((((p1 → (p2 ∧ p4)) ∨ (p1 ∧ p5)) ∧ (False → False)) ∧ True) ∧ p5)))) → p4) ∧ (p4 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134509600024037525914995215406 : (((((p4 ∧ True) → (False → ((True ∧ ((False ∧ p3) → (p2 → ((False ∨ p4) ∨ p2)))) ∧ (p2 ∨ p2)))) ∨ p4) → False) ∨ ((True → p5) → p5)) := by
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
theorem thm_5_vars_117250011823416557522087029737 : ((True ∧ (p5 ∨ (p2 ∧ ((p5 ∧ p1) ∨ (p2 ∧ (p5 ∨ (p3 ∨ ((p1 ∨ p4) ∨ (True ∨ (p5 ∧ ((True → True) ∨ True))))))))))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5058126443362068577043040918 : (((((p3 ∨ ((((((p4 ∧ p2) ∧ ((p4 ∨ p5) ∧ p2)) ∧ p4) → p5) → p3) ∨ ((True → p5) ∧ p1))) → (p1 ∧ p2)) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_842584141878257497047787784 : ((False ∨ ((p2 ∧ p2) → ((p4 → p3) → (((p2 ∨ p1) ∧ (((p5 → p3) → p4) ∨ (p4 ∧ ((p1 ∧ p1) ∨ p4)))) ∨ p2)))) ∨ p3) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51859601327379711335240375341 : ((((((p4 ∧ (p5 ∧ (False ∨ (True ∧ ((p1 ∧ p2) → False))))) ∧ p3) ∨ p5) ∨ False) ∨ ((True ∨ ((p2 → (p5 ∨ False)) → False)) ∨ p3)) ∨ p1) := by
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
theorem thm_5_vars_698353337959442654406165949939 : (((((False ∧ (p2 → ((True ∨ p1) ∨ (p1 ∧ True)))) ∨ (p1 ∧ p5)) ∨ ((p4 ∨ (p2 ∨ (p5 ∧ ((p5 ∨ (p4 ∧ p4)) ∨ p2)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336254106344577563310442947752 : (p1 → ((((p5 ∨ ((p3 ∧ (p4 → p5)) ∧ p3)) ∨ (p2 ∨ ((p4 ∧ (p1 → p1)) → p3))) ∨ ((True ∨ ((p5 ∧ p5) ∨ p1)) ∧ p5)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38533857474631644190001560673 : (((((((p5 → ((p4 → p1) ∧ p4)) ∨ p5) ∧ p5) ∧ False) ∧ (True ∨ (p3 ∨ ((p5 → p4) ∨ (True → ((False ∨ True) ∧ True)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1593757677756391077463756697 : (((p4 ∨ ((False ∨ ((p1 ∧ p3) ∧ (p1 ∨ ((((True ∨ ((p3 ∧ True) → p4)) → p4) ∨ p2) ∨ p3)))) ∧ p4)) ∨ p4) → (False ∨ p4)) := by
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
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- False on the left can always be used.
        apply False.elim h7
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h6
            case inr h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h6
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h6
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187621782676809428892957694728 : ((p4 ∨ (p2 → ((p5 → (True ∨ True)) → ((p3 ∧ p3) → p4)))) → ((p3 → p3) ∧ (p2 → ((False ∧ ((p1 ∨ p2) ∧ False)) ∨ (p2 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146573737152150636036047735038 : ((p5 ∨ (p5 → (p4 ∨ (((((p5 ∨ (p5 → p3)) ∨ ((p2 ∨ p2) → False)) ∧ p5) → (p5 ∧ p2)) ∨ p5)))) ∧ (False → (p1 → (p1 ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205818008780704829982648685821 : (((p5 ∨ True) → ((p4 ∨ p4) ∨ p2)) ∨ (((p3 ∨ p2) → p5) ∨ ((((p5 ∨ p3) → p4) ∨ True) ∨ ((p5 → ((p2 ∧ p3) → False)) ∧ p2)))) := by
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
theorem thm_5_vars_56083526251726865895271531795 : ((((p1 → (p1 ∨ p4)) → p1) ∨ (((p5 ∧ p3) ∨ ((((p2 ∨ (p1 → (p2 → p3))) ∨ p1) → True) ∨ ((p2 ∧ p4) → True))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61780870745614958762579699735 : ((p2 ∧ (((p5 ∧ p4) ∧ (((((p3 → ((False → p1) ∧ p1)) → True) ∧ ((p3 → (p4 → True)) ∧ (p5 ∨ p5))) → p3) ∨ p5)) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806336381979126981364982257140 : (((p4 → (((p5 → False) → ((p4 → (p3 ∨ (False ∨ (p1 → ((p3 ∧ p3) ∨ (p4 ∨ p5)))))) ∧ (p1 ∨ (p1 ∧ (p5 ∨ True))))) ∨ p4)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317955130192963723454703770656 : (p4 ∨ ((p5 ∨ ((p3 ∨ ((p4 → p3) ∨ (((p5 ∧ False) ∧ ((p2 → (True → (True → p2))) ∨ (False → False))) ∨ True))) ∧ (p3 → True))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250021888296827608204112107606 : ((True → p3) ∨ ((p1 ∨ ((p2 ∧ (p1 ∨ ((p2 ∨ ((p2 ∧ p3) ∨ ((False ∨ ((p4 ∨ True) ∧ p5)) → (p2 ∨ p2)))) ∧ p3))) ∨ True)) ∨ p3)) := by
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
theorem thm_5_vars_588844388537677346305050009190 : (((((p1 ∨ ((((((True → True) ∨ p4) ∨ p3) ∨ (p3 ∨ (p5 → (False ∨ False)))) ∨ False) ∧ (False ∧ (p5 → (False ∧ p1))))) ∨ p4) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330952700154709415522963417133 : (True → (p4 → (p1 → (((((p3 ∨ True) ∧ (((p5 → p5) ∨ (p2 ∨ p2)) ∨ True)) ∧ p3) ∨ (((True → (p2 ∧ p2)) ∨ p3) ∧ p4)) ∨ p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657304619777177237066030387082 : (((((p3 ∧ p4) ∧ ((p3 → (p4 → ((p2 ∨ (((((p3 → False) → True) ∧ p2) ∧ p3) ∨ p2)) ∨ (p2 ∧ p2)))) ∨ True)) ∨ (True → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57829855719692694187957372917 : (((p4 ∧ (p3 ∨ p2)) → ((p2 ∧ (p4 ∧ ((True ∨ (p1 ∧ (((p5 ∧ p4) ∨ ((False → p4) → (p5 ∧ p3))) ∧ True))) → p2))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62691617198055035260188284838 : ((p4 ∧ (((((((False ∨ p1) ∧ (p3 → p5)) ∨ ((False ∨ p5) → (((p5 ∨ (p1 ∧ p3)) ∧ p2) ∨ True))) ∧ p5) ∧ p3) → True) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57716022567189694717360771287 : ((((p5 ∧ p3) → p2) → (p4 ∧ (((((p3 → p3) ∧ p2) ∧ (p5 → ((p5 ∧ True) ∨ p3))) ∧ (p3 → (p2 → p4))) ∨ (p1 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166512855742564719594651878487 : ((p4 ∨ (((((p2 → False) → p4) ∧ ((p4 ∨ True) → (p3 ∧ p3))) ∨ p4) ∧ (p3 ∨ p4))) ∨ (((False → (p2 ∧ p3)) → True) ∨ (p4 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58986625024575882574278323349 : (((p3 ∧ True) ∨ ((False ∨ (p5 ∧ ((p2 → p4) ∨ (False ∨ ((p4 ∧ (p1 → (True ∧ True))) → p5))))) ∨ ((p4 ∨ p1) → (False ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341826872036896091045519076487 : (p2 → ((((((p1 ∧ False) → (p4 ∨ p5)) → ((p2 ∧ p3) ∨ p3)) ∧ (p2 ∧ p1)) ∧ ((p3 → (True ∧ (p1 ∨ p5))) ∨ True)) → (p3 ∧ p1))) := by
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
  cases h4
  case inl h9 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∧ False) → (p4 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h13
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h10
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
  case inr h19 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h20 : ((p1 ∧ False) → (p4 ∨ p5)) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h24 := h5 h20
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- One of the premise coincides with the conclusion.
      exact h27
    case inr h28 =>
      -- One of the premise coincides with the conclusion.
      exact h28
  -- Conjunctions on the left can always be decomposed.
  let h29 := h2.left
  let h30 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h31 := h29.left
  let h32 := h29.right
  -- Conjunctions on the left can always be decomposed.
  let h33 := h32.left
  let h34 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h35 =>
    -- One of the premise coincides with the conclusion.
    exact h34
  case inr h36 =>
    -- One of the premise coincides with the conclusion.
    exact h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173147783871437351799413227245 : ((p3 ∨ (((p4 ∨ (p1 ∨ p5)) → ((True ∧ p2) → p5)) → ((p1 ∨ p5) ∧ False))) ∨ ((((p3 → p1) → (p5 ∨ (p2 → p3))) ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591213281946314340022619592956 : ((((((p4 ∧ (p4 ∨ ((((p4 ∨ p2) → (True ∧ p4)) ∨ (p3 → False)) ∧ ((True → p2) ∨ (p2 ∨ p3))))) → p1) ∧ (p2 → True)) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225602962090849376446766644873 : (((p1 → True) ∧ p2) ∨ (((((False → ((False → p2) ∨ p4)) ∧ (p4 ∧ (p1 ∧ p1))) ∧ (False ∨ p3)) ∨ ((p5 → (p3 → p5)) ∨ p1)) ∨ False)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83989263291271589047024539615 : ((((True → ((p4 ∧ (p5 ∧ False)) ∧ (p1 → (p3 ∧ ((p2 ∨ False) ∨ True))))) ∧ p4) ∧ (p3 ∨ (((True → p4) ∨ True) ∧ (True ∧ p1)))) → p2) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h14.left
      let h17 := h14.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h19 := h4 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h14.left
      let h25 := h14.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h27 := h4 h26
      -- We need to get the left conjuct of h27 based on <expert-advice>.
      let h28 := h27.left
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- We need to get the right conjuct of h29 based on <expert-advice>.
      let h30 := h29.right
      -- False on the left can always be used.
      apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39153514870763877481225056288 : ((((p1 ∨ p3) → (p5 ∧ (((True ∧ p4) ∨ p3) ∧ ((p1 ∧ False) ∧ ((True ∧ (True ∧ p2)) ∨ ((p5 ∨ True) → (True ∨ True))))))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112336456824396873884201310749 : (((p4 → (p2 ∨ (((p3 ∧ (True → ((p1 ∨ (p2 ∨ True)) ∨ (p3 ∧ p1)))) → p5) → ((p4 → (p5 ∧ False)) ∨ True)))) ∨ p5) ∨ (p5 ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_768238852676990231185626293036 : (((p5 ∧ ((((True ∨ p2) → ((((p2 → True) ∨ p2) → (p3 → ((p5 ∨ p3) ∧ (False ∨ p4)))) ∨ True)) ∧ True) ∧ (p4 → (p5 ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862645823229456403188225144362 : (((((((((True → (p5 ∨ p2)) ∨ False) ∧ ((p5 ∧ False) ∨ (p1 ∧ p1))) ∧ False) ∨ p5) ∨ (p5 → (p2 ∨ (False → (True ∧ p5))))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((True → (p5 ∨ p2)) ∨ False) ∧ ((p5 ∧ False) ∨ (p1 ∧ p1))) ∧ False) ∨ p5) ∨ (p5 → (p2 ∨ (False → (True ∧ p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167217755378885205939443261950 : (((p2 ∨ (p3 → ((p3 ∨ ((((p2 ∨ p4) ∧ (p2 ∧ p3)) ∧ p5) → p5)) ∧ True))) ∨ False) → (((p1 ∧ p5) ∨ (p3 ∨ p4)) ∨ (p4 → p4))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115925882276893558070187788004 : (((True ∧ ((p4 ∨ p5) ∧ p3)) ∨ ((p2 ∧ ((p3 ∨ (True ∧ (p3 → (p4 ∧ p1)))) → False)) ∧ ((False → (p4 → p3)) ∨ True))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61601509502866831654711366154 : ((p1 ∧ ((p2 ∧ (p1 ∧ p1)) → (((p1 → p5) ∧ ((p4 ∧ ((p1 → (p3 ∨ p4)) → False)) ∨ (p3 ∨ p3))) ∨ (False → (True ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16169375526660562650425931453 : ((((p4 ∧ ((((((p4 ∨ True) ∨ ((p3 ∧ ((p4 ∧ p3) → p1)) ∨ p2)) ∨ p5) ∧ p4) ∨ True) ∧ p2)) ∨ True) ∧ ((p4 ∨ True) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341397444280183870387418588040 : (p2 → (((p3 → p4) ∧ ((((False ∨ (p4 ∨ (False ∧ ((True → ((False ∨ p5) ∧ p4)) ∨ p3)))) ∨ p4) ∨ (p5 → (False → p3))) → False)) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (((False ∨ (p4 ∨ (False ∧ ((True → ((False ∨ p5) ∧ p4)) ∨ p3)))) ∨ p4) ∨ (p5 → (False → p3))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h5
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53965181825829451512698342492 : (((((True → (p4 ∧ p1)) ∨ (True ∧ (p3 ∨ True))) ∧ p4) → (((((p3 ∧ p4) → (p4 → p2)) ∧ p2) ∨ (p3 ∧ p5)) → (False ∨ True))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309345814532987095342464911456 : (p2 ∨ (((p4 → (p1 → (p2 ∧ (((True ∧ False) ∨ p2) ∧ ((p5 ∧ (p3 ∨ True)) ∧ True))))) ∨ ((p4 ∧ True) → (True ∨ False))) ∨ (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191050509771925100998200979892 : ((((True → p5) ∨ (p3 → False)) → (p3 ∧ (p5 → p2))) ∨ (True ∧ ((p5 ∧ (p2 ∧ (p3 ∨ p4))) ∨ ((True ∨ p2) → ((p2 ∧ False) → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256986492378919873398396237402 : ((p1 ∨ p5) → (p1 ∨ (p2 ∨ (((p3 → p4) → ((p4 ∨ p4) ∧ (False → (((p4 ∧ (False ∨ (p5 ∨ p5))) ∨ p2) → p3)))) ∨ (False → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138364505144181960280203570501 : ((p4 → (((((p3 → (True → (((p5 ∨ p4) ∧ False) ∨ p2))) → False) ∨ p2) ∨ p2) ∧ ((p4 → (False ∨ True)) ∨ False))) ∨ (True ∨ (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210411515658741915109583785461 : (((p3 ∨ (True ∧ True)) ∨ False) ∧ ((True → (((p2 → (True → (p4 → (p5 ∨ p2)))) → (p4 ∧ (p2 ∧ (p4 ∨ p5)))) → p5)) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784576527290832328851086064112 : (((p3 ∨ (p1 ∨ ((((True ∧ ((p2 ∧ p2) ∨ p5)) → (p5 ∧ (((p5 ∨ p4) ∧ p1) ∨ p4))) ∨ True) ∨ (p3 ∨ ((False ∧ p3) ∧ p4))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135456548156295732903953755143 : (((((((True ∧ ((p2 ∨ p2) ∨ ((p4 ∨ p5) ∧ True))) ∨ (True ∧ p5)) ∨ p3) → p4) → p4) → (p3 ∧ (False ∨ p1))) ∨ ((p3 ∨ True) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



