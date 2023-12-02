variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47433526339753357491189413437 : (((p2 ∧ ((((p4 ∧ p2) ∨ ((False ∨ p5) ∧ p3)) ∨ False) ∧ ((((p3 ∨ (p4 → p1)) → False) → True) ∨ (p1 ∨ p2)))) ∨ (False ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65227249898690539788250937863 : ((p3 ∨ ((p5 ∧ ((((True → False) ∧ (p1 ∨ (p2 ∨ False))) ∨ ((p1 ∨ (p1 ∨ p2)) ∨ p5)) ∨ (p1 ∨ ((p2 → False) → True)))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147909118321393764513080788133 : (((((((True → p4) → ((p5 ∨ (True → p1)) ∨ (p1 → p2))) → False) ∧ p5) ∧ (p1 → p1)) ∧ (p5 ∧ True)) ∨ ((p2 → False) → (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47265697758889634324012601070 : ((((((p5 → p3) → p2) ∧ True) ∧ ((True ∧ (((p3 ∨ ((p3 ∨ p1) → (True ∧ (True ∧ p4)))) → p3) ∧ p4)) ∨ p4)) ∨ (True ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186471571681555577223603870621 : (((((p5 ∧ (False → p5)) → False) ∨ (p3 → p2)) ∧ (p2 ∨ p5)) → (((p3 → p5) ∧ ((False ∨ p1) ∧ (p2 ∨ p2))) ∨ ((True ∨ p1) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113078733154044054611423259715 : (((p4 ∨ ((((p5 ∨ (p1 ∧ ((p1 → (p4 ∧ (((p1 → p1) ∧ (True ∧ p3)) ∧ p4))) ∧ p5))) ∧ True) → p1) → p2)) → False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174441155095225666018781395469 : ((((True ∨ ((False ∧ (True → p4)) → p3)) → p4) → ((p3 ∨ p2) → (p3 ∧ False))) → ((p4 ∧ ((p2 ∨ ((p5 → p3) ∧ p2)) ∨ p2)) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h7 : ((True ∨ ((False ∧ (True → p4)) → p3)) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h10 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h11 := h1 h7
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p3 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h13 := h11 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h18 : ((True ∨ ((False ∧ (True → p4)) → p3)) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h21 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h22 := h1 h18
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : (p3 ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
  case inr h26 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h27 : ((True ∨ ((False ∧ (True → p4)) → p3)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h3
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h31 := h1 h27
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : (p3 ∨ p2) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h33 := h31 h32
    -- We need to get the right conjuct of h33 based on <expert-advice>.
    let h34 := h33.right
    -- False on the left can always be used.
    apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147568830171204802266990484277 : ((((((p2 ∨ (p2 ∧ p5)) ∧ (p1 ∨ (p1 → (p3 → p1)))) ∨ ((p1 ∨ (p4 ∨ p2)) → False)) ∧ p2) → p4) ∨ ((False → p3) ∨ (p4 ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62442270829430926145711107108 : ((p3 ∧ (((True ∨ True) ∧ p4) ∨ ((p4 ∨ (((p4 ∧ ((p5 ∨ p2) ∧ (True ∨ (p5 ∧ (p1 → p3))))) → (p1 → p1)) ∨ p4)) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41727116271415769609806500093 : (((((p1 → (p4 ∧ p3)) → p4) ∧ (True ∧ (((p5 → False) → True) → ((p3 → (p4 ∧ False)) ∧ (p3 ∨ ((p3 → True) ∧ p2)))))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118107870752431455529752191446 : ((False ∨ ((p5 ∧ ((p2 ∨ (True ∧ ((p5 ∧ (p3 ∨ (((p2 → True) ∧ (p5 ∧ p5)) → True))) → True))) → (p3 ∨ False))) ∨ p2)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309309611440845460439374423549 : (p2 ∨ ((((p3 → (((p1 → (True → False)) → p3) ∨ ((p1 → (((p3 ∧ True) ∧ True) ∨ (p4 ∨ True))) ∧ p4))) → p5) ∨ p3) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204125784489963564178253747169 : ((((p1 ∧ (p5 ∧ p5)) ∧ p4) ∧ p5) ∨ ((p4 ∧ ((p5 ∨ p4) → (True ∨ (p4 → ((False → ((True → p3) → True)) ∨ (p2 ∧ p2)))))) → p4)) := by
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
theorem thm_5_vars_161455651391095540291499611414 : ((p3 ∧ (((p4 ∧ ((((p5 ∧ p5) → p4) → p2) ∨ False)) ∧ (p5 ∨ ((p3 → p5) ∨ p5))) ∨ p3)) → (p4 → (p1 ∨ ((p1 ∧ p3) ∨ True)))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645848564075805840231966108716 : ((((True → ((((p1 ∧ (p3 → False)) → ((p5 ∧ (p3 ∧ p1)) ∨ (True ∧ ((p3 → (p1 ∨ (p4 ∧ True))) → False)))) ∧ p5) ∧ p1)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199862790741455633851238921277 : (((p4 ∨ ((False → False) → p2)) ∧ (True ∨ False)) → ((p3 ∧ p2) ∨ ((False ∧ (False ∨ p2)) ∨ ((False ∧ p5) → (p3 ∧ ((False ∨ p4) ∧ p3)))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
      -- False on the left can always be used.
      apply False.elim h9
      -- Conjunctions on the left can always be decomposed.
      let h11 := h6.left
      let h12 := h6.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h19 := h16.left
      let h20 := h16.right
      -- False on the left can always be used.
      apply False.elim h19
      -- Conjunctions on the left can always be decomposed.
      let h21 := h16.left
      let h22 := h16.right
      -- False on the left can always be used.
      apply False.elim h21
    case inr h23 =>
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_723786901261979387208363296078 : (((((p2 → p5) → p5) ∧ (p2 ∧ (p5 ∨ (((True → (p3 → (p1 ∨ ((False ∧ (p3 ∨ (p4 → p3))) ∨ p3)))) ∨ (p3 ∧ False)) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207037162784283465895047409987 : ((((p5 ∨ p2) → (True ∨ p3)) ∧ p5) → (((((p4 ∨ ((p5 ∧ (p2 ∧ (p4 ∨ False))) ∨ p2)) ∧ True) ∧ (p1 ∧ (p5 → False))) ∨ p5) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69181599970601726321586915480 : ((p5 → ((True ∧ (p4 ∨ (((False ∧ (p5 → (p1 → (p2 ∧ p5)))) ∨ p4) ∧ p3))) ∨ (p3 → ((((p3 ∧ p3) → p5) ∧ p1) ∨ p5)))) ∨ p3) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178094432904596358421859802330 : ((((p4 ∨ ((True ∧ (p2 ∨ p2)) ∧ (p4 ∨ (p4 → False)))) → p4) → p4) ∨ (False → ((p1 ∨ p1) → ((p2 → (p1 → False)) ∨ (True ∨ p3))))) := by
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
theorem thm_5_vars_8487176447882873264352184699 : ((((((((p5 ∨ p4) ∧ (((p3 → p2) → (((True ∧ p1) ∧ True) → p5)) ∧ p4)) ∨ (p4 ∨ p1)) ∧ p5) ∧ False) ∧ (p1 ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191498262579021083637117944357 : ((True ∧ (p5 → (((p1 ∨ True) ∧ (p2 ∧ False)) ∧ p2))) ∨ ((((False → (p3 ∧ True)) → (False ∨ p5)) ∧ p3) ∨ (p2 ∨ ((False → p3) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_191647246179980808211889331738 : ((p4 ∧ ((True → p2) ∧ (((p4 ∨ p5) ∧ p1) ∧ p3))) ∨ ((((p3 ∨ ((p3 → ((False → (p5 → p4)) ∧ False)) ∨ p2)) ∧ p4) ∨ p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111424809366522409613917334606 : (((p4 ∨ ((((True → (p1 ∧ (False ∧ p5))) ∧ (p2 ∧ p4)) ∨ (((p2 → p1) ∨ False) → ((p4 ∨ p4) ∨ p5))) ∨ False)) ∧ False) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613711117270014901501414520015 : (((((((p1 ∧ p1) → p3) → (((p3 ∨ (((p4 ∨ p5) ∨ p2) ∨ p3)) ∨ ((p2 ∨ p5) ∧ True)) ∧ p1)) ∧ ((p4 → p4) ∨ p3)) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230307314311232137600747192123 : (((p1 ∨ p3) ∧ True) → ((((p1 ∧ True) → ((p3 ∧ p5) ∧ (p4 → p3))) ∧ (p1 ∧ (True ∨ (p2 ∨ (p2 ∧ True))))) → (p5 ∧ (p3 ∨ False)))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h10
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h5
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h21 =>
      -- Conjunctions on the left can always be decomposed.
      let h22 := h1.left
      let h23 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h24 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h25 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h24
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h26 := h3 h25
        -- We need to get the left conjuct of h26 based on <expert-advice>.
        let h27 := h26.left
        -- We need to get the right conjuct of h27 based on <expert-advice>.
        let h28 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h30 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h31 := h3 h30
        -- We need to get the left conjuct of h31 based on <expert-advice>.
        let h32 := h31.left
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- Conjunctions on the left can always be decomposed.
      let h37 := h1.left
      let h38 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h39 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h40 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h39
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h41 := h3 h40
        -- We need to get the left conjuct of h41 based on <expert-advice>.
        let h42 := h41.left
        -- We need to get the right conjuct of h42 based on <expert-advice>.
        let h43 := h42.right
        -- One of the premise coincides with the conclusion.
        exact h43
      case inr h44 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h45 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h5
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h46 := h3 h45
        -- We need to get the left conjuct of h46 based on <expert-advice>.
        let h47 := h46.left
        -- We need to get the right conjuct of h47 based on <expert-advice>.
        let h48 := h47.right
        -- One of the premise coincides with the conclusion.
        exact h48
  -- Conjunctions on the left can always be decomposed.
  let h49 := h2.left
  let h50 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h51 := h50.left
  let h52 := h50.right
  -- Disjunctions on the left can always be decomposed.
  cases h52
  case inl h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h1.left
    let h55 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h56 =>
      -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
      have h57 : (p1 ∧ True) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h56
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h49, we can now drive its conclusion.
      let h58 := h49 h57
      -- We need to get the left conjuct of h58 based on <expert-advice>.
      let h59 := h58.left
      -- We need to get the left conjuct of h59 based on <expert-advice>.
      let h60 := h59.left
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h60
    case inr h61 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h61
  case inr h62 =>
    -- Disjunctions on the left can always be decomposed.
    cases h62
    case inl h63 =>
      -- Conjunctions on the left can always be decomposed.
      let h64 := h1.left
      let h65 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h64
      case inl h66 =>
        -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
        have h67 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h66
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h49, we can now drive its conclusion.
        let h68 := h49 h67
        -- We need to get the left conjuct of h68 based on <expert-advice>.
        let h69 := h68.left
        -- We need to get the left conjuct of h69 based on <expert-advice>.
        let h70 := h69.left
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h70
      case inr h71 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h71
    case inr h72 =>
      -- Conjunctions on the left can always be decomposed.
      let h73 := h72.left
      let h74 := h72.right
      -- Conjunctions on the left can always be decomposed.
      let h75 := h1.left
      let h76 := h1.right
      -- Disjunctions on the left can always be decomposed.
      cases h75
      case inl h77 =>
        -- We want to use the implication h49 based on <expert-advice>. So we show its premise.
        have h78 : (p1 ∧ True) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h77
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h49, we can now drive its conclusion.
        let h79 := h49 h78
        -- We need to get the left conjuct of h79 based on <expert-advice>.
        let h80 := h79.left
        -- We need to get the left conjuct of h80 based on <expert-advice>.
        let h81 := h80.left
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h81
      case inr h82 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h82



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198832369986811646458979415281 : ((p1 → ((p2 ∨ p4) ∧ (True ∧ (p4 → True)))) ∨ (p2 → ((p3 ∨ (True ∧ ((((True → False) ∧ True) ∧ (p4 ∨ (p2 ∧ True))) → p3))) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h14 := h5 h13
    -- False on the left can always be used.
    apply False.elim h14
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352058180595430066234325506314 : (p4 → (((((p5 ∧ False) → True) → False) ∨ True) ∧ (((p3 → (False ∧ (p4 ∨ (p3 ∨ True)))) ∧ ((p3 ∧ p4) ∧ True)) → ((False ∨ True) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h2.left
    let h7 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h12 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h13 := h6 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668848926127635044803536702296 : ((((((True ∧ (p4 ∧ (p1 ∨ False))) ∧ ((p4 ∨ p1) ∧ (((p3 ∨ p4) → (p1 ∧ (p1 ∨ p4))) ∧ True))) ∨ True) ∨ ((p5 ∧ False) ∧ p1)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_135673861134100461983374502079 : (((False → (p5 → (((((p5 → p5) → (p5 ∨ False)) ∨ (p1 → False)) ∨ True) → p4))) → (True → (p4 → (p4 ∨ p1)))) ∨ (False → (p2 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205117616787880895153411174063 : ((((p4 ∨ p3) ∨ p2) ∧ (False ∧ p2)) ∨ (True ∨ ((True ∧ (((p5 ∧ p3) ∧ p2) ∨ False)) ∨ (p2 ∧ (p3 ∧ (p1 ∨ ((p3 → False) ∧ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233168944480955096366450708786 : ((p5 ∧ (False ∨ p5)) → (True ∧ (((p1 ∨ (p5 ∧ p5)) ∨ p2) ∧ (((p2 ∧ p1) ∧ False) ∨ ((p4 ∨ ((p5 ∨ True) ∨ p1)) ∧ (p1 → p5)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- One of the premise coincides with the conclusion.
    exact h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53973376408590833696554638726 : ((((p5 ∨ ((p4 → (p5 → (p3 ∨ False))) → p2)) ∧ p4) → ((p4 ∧ (((p2 → ((p2 ∧ p5) → (p5 → p4))) → p2) ∧ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923526121171455621544205548837 : ((((((p4 ∧ p1) ∧ ((False ∨ True) ∨ p4)) ∧ ((p4 ∨ p4) → False)) ∧ ((p3 ∨ (p1 ∨ p4)) → ((p3 ∨ (p1 → p5)) ∧ (True → p2)))) → False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : (p4 ∨ p4) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h16
    -- False on the left can always be used.
    apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694695985671195291018706406747 : ((((p1 ∨ (p5 ∨ (False ∧ ((p3 ∧ (p4 ∧ p1)) ∨ ((p5 ∨ False) ∨ p5))))) ∨ (p4 → ((p1 ∧ p2) ∨ (True → ((p2 ∨ False) ∧ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149565227513483309648824667852 : ((p2 ∧ (True ∧ (((p2 → False) ∧ ((p1 → (False ∧ p3)) ∧ ((p2 ∨ p2) ∧ p5))) ∨ (p5 ∨ (True ∨ p3))))) ∨ (((False ∧ True) ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247747172480764641807946019423 : ((p1 ∨ False) ∨ ((True → p2) → ((True → (((p1 ∧ (p4 ∧ p1)) ∨ ((p1 → (False ∧ p1)) → p2)) → ((True ∧ p3) ∨ p1))) ∨ (p1 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44336796410684102795622213397 : ((((((p2 ∨ p2) ∨ ((False → p5) → ((p5 ∧ p4) ∧ (False ∧ (p2 ∧ p3))))) → p2) → ((p4 ∧ p3) → ((p2 → p2) → p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203774404380200795071693738279 : ((p5 ∨ (p5 → (False → (p1 → p4)))) ∧ (p1 ∨ (((p5 → (p3 ∧ p3)) ∧ ((p3 ∨ (p5 ∧ (p2 ∧ True))) ∨ p2)) ∨ (False → (p5 ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259615388250421149400161038049 : ((p1 → False) → (((((p5 → p3) → False) ∨ ((p5 ∧ p5) → p4)) ∨ ((((True → p1) → p4) ∨ ((True → p3) ∨ p3)) ∨ (p5 ∧ p5))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319373551615954751568084554857 : (p4 ∨ ((((p1 → True) ∧ p2) → (True → (((p2 → p4) ∧ (True ∧ p3)) ∧ p4))) ∨ ((((((p2 → False) → True) ∧ p1) ∧ True) ∧ False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112263148746045492998069224015 : (((p5 ∨ (((((((p5 → p2) → (False ∨ (True → (p2 ∨ False)))) ∨ (p3 ∧ (True ∧ p5))) ∨ True) ∧ p3) → p4) → p2)) ∨ True) ∨ (True ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659992284869972911608637137252 : (((((((((((True ∧ p5) ∨ p1) → p2) → (False ∨ p5)) ∨ (((p5 ∧ False) ∨ False) ∧ (p5 ∨ p1))) ∧ True) → p1) ∨ False) → (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735478729165509453953997749917 : ((((p4 ∨ p4) ∧ ((True → (((((((p2 ∧ (p4 ∨ p4)) ∧ True) ∧ ((p3 → True) → p2)) → p3) ∧ p2) → p2) ∧ (p1 ∨ p5))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608264877341971091382634210892 : ((((((((p1 ∧ (((p3 ∧ p4) ∨ ((p1 → p1) ∧ p2)) ∨ ((p1 ∧ p1) ∧ p5))) → (True ∧ (p5 ∧ False))) → p1) ∨ p2) ∨ p2) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_179199243510766588307864622867 : ((p3 ∧ (p1 ∨ (((True ∧ (((p5 ∧ p3) → p3) → p3)) ∨ p3) → p1))) ∨ ((p1 ∨ (p4 ∧ (True ∧ False))) → (True ∧ (False → (p1 → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705363032976246887669703980144 : ((((((False ∧ (False ∨ p1)) ∨ (False ∧ p1)) ∨ p1) ∧ (p3 ∧ (True ∧ (((False → p2) ∧ (p1 → ((p2 ∨ True) ∧ p2))) ∨ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199468937403158754843487601148 : (((False ∨ (True → ((p2 ∧ p5) ∧ p4))) ∨ p4) → (((p5 ∨ p4) ∧ ((p2 → ((p1 ∧ p5) → p5)) ∨ p2)) → (p2 → ((False ∧ p4) ∨ p4)))) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
          have h11 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h10, we can now drive its conclusion.
          let h12 := h10 h11
          -- We need to get the right conjuct of h12 based on <expert-advice>.
          let h13 := h12.right
          -- One of the premise coincides with the conclusion.
          exact h13
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- False on the left can always be used.
          apply False.elim h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
          have h19 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h18, we can now drive its conclusion.
          let h20 := h18 h19
          -- We need to get the right conjuct of h20 based on <expert-advice>.
          let h21 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h25
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
      case inr h33 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114827161452841248695838034914 : (((p2 ∨ (True → (((p4 ∨ (False ∧ p3)) ∨ (p4 → p1)) ∧ (p3 ∨ False)))) ∧ ((((p5 ∨ (p3 ∧ p3)) ∨ p3) ∧ False) ∨ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116908780133386226010505137324 : (((p5 → p4) ∨ (((p3 → ((p1 ∨ ((p5 ∧ (p4 ∧ (p5 ∧ p3))) ∧ (True → True))) → False)) → ((p4 → p2) ∨ p3)) ∧ p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659926957274864878821337722544 : ((((((p2 ∧ ((((p2 → p1) ∧ ((p3 ∧ p3) → p4)) ∧ True) → (p1 ∧ (p3 ∧ ((True ∨ p2) ∧ p1))))) ∧ p4) ∨ p3) → (p2 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759080814511173760833963343580 : (((p2 ∧ (((((p3 ∨ (p3 → (True ∨ (False ∧ p3)))) → p5) ∧ ((False → ((True → p5) ∧ (p1 ∨ p4))) → p1)) ∧ p4) ∧ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168411276893334877595170364793 : (((p2 ∧ True) → ((((p2 → p5) ∧ p4) → (((p2 ∧ p5) ∨ True) ∨ True)) → (p1 ∧ p3))) → ((p1 ∨ ((p2 ∨ (p5 ∧ p2)) → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177848910493871287512511338567 : ((((p1 → ((((p3 ∧ p1) ∨ p3) → True) → (p1 → p3))) ∧ p2) ∨ True) ∨ (((p1 ∨ p4) ∨ p3) ∨ (p5 → ((p2 → p5) ∧ (p5 → p2))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68581465122575293872053429471 : ((p4 → (((p5 ∧ (p3 ∨ p1)) ∨ ((p4 ∨ p5) → (p2 → (p2 → (((True ∨ p4) ∧ p1) ∨ (p4 → ((p3 → p4) ∧ True))))))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594726167190324216523682910599 : ((((((p2 ∨ True) ∧ (p4 ∧ (((p5 → (p2 → (False ∨ p4))) ∧ (p3 → p5)) → False))) → (((False → p5) → p3) ∨ (p3 ∧ p4))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250693799273008531295786880672 : ((p1 → False) ∨ ((((p2 ∧ p2) → (((p4 ∧ p1) ∧ p5) → p4)) → ((((p5 ∨ p4) → (False → p4)) ∧ (False ∨ p1)) ∧ (p4 ∨ p2))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ p2) → (((p4 ∧ p1) ∧ p5) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134346005273486141670104951899 : (((p5 ∧ ((p3 ∧ (False ∧ p4)) ∧ (p5 → (((p4 ∨ (p5 → ((p4 ∧ p1) ∨ (p4 → p2)))) ∧ True) → p5)))) ∨ p5) ∨ ((p4 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198460875025080444184572087854 : ((p5 ∧ ((p1 → p3) ∨ ((True → False) ∧ p4))) ∨ ((((p5 ∨ p2) ∨ (False ∧ ((False ∧ (False ∧ False)) ∨ ((p3 → p3) → p5)))) ∨ True) ∧ True)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134057576111434471349958448736 : ((((p1 → (p4 ∧ (p3 → (False ∧ (p5 ∨ (p1 ∧ (p3 ∨ (((False ∨ False) → p4) ∧ (p3 ∨ False))))))))) ∨ p2) ∨ p2) ∨ ((False ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56756788911228678375103351197 : ((((p3 → p2) ∨ p4) ∧ (True ∧ (False ∨ (((True ∧ (((p3 ∨ (p5 ∧ p4)) ∨ p1) ∧ p4)) ∨ (((p3 ∧ p4) → p4) ∧ p1)) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216248846558333840677562966613 : ((p1 → (p3 ∧ (p2 ∨ p1))) ∨ ((((((p2 ∧ False) → ((p5 ∧ True) ∨ p4)) ∨ p3) → p1) ∨ (False → (False ∨ ((p4 ∨ True) → p4)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_471894501165507972454201842123 : (((((((p4 ∨ True) → (p3 ∧ p4)) → p5) ∧ (p5 → (True → False))) ∨ (True ∧ (p2 ∨ (p5 ∨ (p4 → (p1 → (p4 ∨ (p2 ∨ p3)))))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760395336033376969093399443695 : (((p2 ∧ ((p4 → p4) → (((p5 → ((True ∨ p4) ∧ ((True ∨ p5) ∨ p2))) ∨ (False → p5)) ∧ (((p3 → p1) ∧ True) ∧ (p3 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193343384845214983382140126172 : ((((p1 → p2) ∨ p5) → (p2 ∨ ((p5 ∨ True) ∨ p4))) → (((True → False) ∨ ((False → ((p1 → p3) ∧ False)) ∨ p2)) ∨ ((p5 → False) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135145440708023115197003117612 : (((p4 ∨ ((p2 ∧ p4) ∨ ((((True → ((False → (p4 ∨ (p1 → p3))) → False)) → False) ∨ p3) ∧ p2))) ∨ (p4 → True)) ∨ (p4 ∧ (p2 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184519984303440334519346618835 : (((p2 ∨ (((p2 ∨ p1) ∧ (p4 ∨ p1)) ∧ p1)) ∨ (False → p1)) ∨ (p3 ∧ (((p1 ∨ p4) ∧ (p3 ∧ (True → p4))) → ((True ∧ p2) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684313340621120216365195616920 : ((((((p2 ∧ (((p2 → (p3 → p1)) → True) ∨ p4)) ∧ (p3 ∧ p2)) → ((p2 → False) ∨ p4)) ∨ ((p4 → (p4 → p2)) ∧ (p2 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114643771379943672801772003068 : ((((((((p3 → (True ∧ p5)) ∧ p2) ∨ p5) ∨ p4) ∨ (p1 → p4)) ∨ (p2 → p4)) ∨ (((True ∧ p2) → (False → p4)) ∧ p1)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164451938722376990121161036140 : (((((p2 ∧ ((p4 ∨ p5) ∧ p3)) ∧ (False → ((p3 ∨ p1) ∨ (p4 → p3)))) ∧ p4) ∧ False) ∨ ((True → (False ∧ (p1 ∧ p3))) → (True ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245041997110011821307838483478 : ((p1 ∧ p5) ∨ ((False ∨ (((p3 → False) → (p5 ∧ (p4 ∨ ((p4 ∨ (p3 → ((p5 ∨ p5) → False))) → False)))) → (p1 ∧ (p4 → True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258675482292519966027579880913 : ((p5 ∨ p5) → ((p1 → True) ∧ (((p4 → ((p5 → (p2 ∨ (p3 ∨ p4))) → (p4 ∧ ((False ∨ ((False ∧ True) ∧ p4)) ∧ p5)))) → False) ∨ p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205599271385180574169327754376 : (((p4 → p5) ∧ ((p2 → p3) → p4)) ∨ (((p1 ∨ p2) ∨ ((p1 ∨ p2) → (((p4 → p2) → True) → (p5 → (p5 ∨ (p5 ∨ p3)))))) ∨ p2)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147931974600507591771618968894 : ((((p5 → ((p2 ∨ (True → True)) ∨ p5)) → ((p3 → ((p4 ∨ p4) → False)) ∧ (p2 ∧ p5))) ∧ (p2 ∧ p3)) ∨ ((False ∧ (p2 → False)) → False)) := by
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
theorem thm_5_vars_47411336578252035345802087886 : (((False ∧ (((True → p1) → ((p1 ∧ p5) ∧ (p4 ∧ (p5 → p2)))) ∨ (((p5 ∨ (p3 → False)) ∧ (True ∧ True)) ∨ p2))) ∨ (p1 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184596204772311608395723636575 : (((p3 → (False → ((False ∨ True) → (True ∨ p3)))) → (False ∧ p2)) ∨ ((p3 → (((p2 → p4) → False) ∨ True)) ∨ ((p2 ∧ True) ∨ (p1 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141238716461656197627343456666 : ((((p3 ∨ (p3 → True)) → (p3 ∨ True)) → (p2 ∧ ((((p3 → p3) → (p4 ∨ p1)) ∧ (True → (p4 ∨ p2))) ∨ p4))) → ((False ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∨ (p3 → True)) → (p3 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h11 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- One of the premise coincides with the conclusion.
      exact h12
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h13 := h9 h11
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_589939861889398685401718173262 : ((((((p1 ∨ ((p2 → (True ∨ (((p3 ∧ ((True ∨ p3) → True)) ∨ p1) ∧ p4))) → False)) ∧ ((p4 ∧ (p4 ∨ True)) ∨ p5)) → p3) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57602725622264086599283726659 : ((((p2 → p4) ∧ p3) → ((p1 → p2) ∧ ((p5 ∨ (p1 ∧ (((((p1 ∧ p1) ∧ (p2 ∧ p5)) → p1) ∧ True) ∨ p3))) → (p1 ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663940493611546236029040104442 : ((((p4 ∧ ((p3 ∨ (True → (p2 ∧ ((p3 → False) ∧ p1)))) → (((p3 ∧ p3) ∧ (p2 → (True → True))) ∧ (p5 ∨ p3)))) → (p3 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197087016973698638646412950653 : (((p1 ∧ (False ∨ ((p1 ∧ p3) ∨ False))) ∨ True) ∨ (((True → p5) ∨ ((p5 → (p2 ∧ True)) ∧ ((True ∨ (False → (True → p5))) → False))) ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322488334433318679095081790837 : (p5 ∨ (((p5 ∨ p1) ∨ ((p3 ∨ (p1 ∨ ((p5 ∧ (((p3 ∨ p3) ∧ p3) ∨ p4)) → (p5 ∨ p3)))) ∧ (True ∨ (p5 → (True ∨ p2))))) ∨ False)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153391566123017695767492163975 : ((p3 ∨ ((p4 ∨ ((p5 ∨ p5) ∨ ((p4 ∧ ((p2 ∨ p5) ∨ p4)) → (p1 ∧ (False → True))))) ∧ (p3 ∨ p3))) → (p5 ∨ ((p5 ∨ True) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
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
          cases h5
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
          case inr h13 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h11
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h5
          case inl h15 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
          case inr h16 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h14
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323670170741731298920043688159 : (p5 ∨ (((((p4 → True) ∨ p4) ∧ (p5 ∨ p5)) ∧ ((True ∧ ((p2 ∧ (p1 ∧ (p4 ∧ p4))) ∧ True)) ∧ p2)) ∨ ((True ∨ p3) ∨ (p4 ∧ p2)))) := by
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
theorem thm_5_vars_300819962931780538002969898654 : (False ∨ (((True → (p4 ∨ False)) ∧ (p3 ∨ (((p1 ∧ p1) → (p3 → p2)) → (p5 ∧ p4)))) → ((p5 → (p5 → ((p1 → p5) → p4))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h13
    -- Implications on the right can always be decomposed.
    intro h14
    -- Implications on the right can always be decomposed.
    intro h15
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h19 =>
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607224485921933578575288705615 : (((((((p1 → (p5 ∧ p4)) ∧ p1) ∨ (p4 ∨ ((p3 ∧ (((p2 ∧ p3) ∨ (p2 ∧ (False ∨ p4))) ∧ (p3 → p3))) ∧ p2))) ∧ p1) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54300526355568692581340772474 : ((((True ∨ p3) ∨ (((p2 → p3) → p3) ∧ p2)) ∧ (False ∨ (((p4 → (True ∨ ((False ∨ p1) → (p1 → True)))) → p2) ∨ (True → True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50130939356758986013977312155 : (((p4 ∨ ((p2 → (True → (p2 ∨ (p1 ∨ p4)))) ∧ ((p3 ∧ (p1 → True)) → (p4 ∧ (p3 → p3))))) ∧ (((p5 → p1) ∧ p2) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303830841123604618277210184855 : (p1 ∨ (((p3 ∧ ((p1 ∧ False) ∧ (((((((p4 ∨ True) ∧ p5) ∧ False) ∧ (p1 → p3)) ∨ True) → (True → p5)) → False))) ∧ (p2 ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55068732323737512699432003828 : (((p4 ∨ ((p5 ∨ (p4 → p3)) → p4)) ∧ (p3 ∧ (((((p2 → p4) ∨ p1) ∨ ((False ∧ p5) → False)) → False) → ((p1 ∧ p3) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2278672253543424126974114123 : (((((p1 → False) ∨ False) ∨ (p3 ∨ (p2 ∨ (True ∧ p3)))) ∧ (p1 → False)) ∨ ((p1 ∨ (p1 → True)) ∧ ((True ∧ True) → (p4 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914794519340974116149254152847 : (((((False ∨ p1) ∨ (((False ∧ (False ∨ p4)) ∨ p3) ∧ (True ∨ ((p1 → p5) → p3)))) ∧ (((p1 ∧ p4) → p1) → ((False → True) ∧ False))) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : ((p1 ∧ p4) → p1) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h7
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h20 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h21 : ((p1 ∧ p4) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h25 := h3 h21
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h28 : ((p1 ∧ p4) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h29
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- One of the premise coincides with the conclusion.
          exact h30
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h32 := h3 h28
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37630827582434100964135422124 : (((((((((((False ∧ False) ∨ (p4 → p5)) → p4) → p3) ∨ ((False ∨ p1) ∨ (True → p1))) → True) ∨ (p3 → p3)) ∨ p4) → p2) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184863874298958806324769961394 : ((((True → False) ∨ p4) ∧ ((p4 ∧ ((p5 ∨ p4) ∨ True)) ∨ p2)) ∨ (p5 → ((True → p1) ∨ (False → (((True ∨ p5) ∨ p1) ∧ (p1 ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57838556059409119015693369621 : (((p5 ∧ (True ∨ True)) → ((((p3 ∨ ((p5 ∨ ((True ∨ p3) ∨ (p3 ∧ (p3 → p3)))) → (True → p5))) → (p4 → True)) → False) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674521315683206521536642978377 : ((((p5 ∨ ((((((p3 ∨ p1) ∨ ((p3 → p2) → (p1 ∨ True))) ∨ p2) ∧ (p4 ∨ p4)) ∨ p4) → (p2 ∨ False))) → ((p3 ∨ p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_92633573322342632410744661263 : (((False → p4) → (((p3 → ((False ∨ p5) ∨ True)) → ((((((True → False) ∨ ((p4 ∧ p2) ∨ p3)) → p3) ∨ p4) ∨ True) ∧ False)) ∧ True)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p4) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p3 → ((False ∨ p5) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722375190527900139907831574784 : (((((p4 ∧ True) ∧ p3) ∧ (p5 ∨ (((((p5 → p5) ∨ p4) → p3) → ((((False → p4) → p2) ∧ p1) ∨ False)) ∧ ((True → p4) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247335652904481940242087815234 : ((False ∨ False) ∨ (p1 → ((((p1 ∧ ((((p3 → p2) ∨ True) ∨ (True ∨ p4)) ∧ ((p2 → p3) ∧ (p5 ∨ True)))) ∧ True) ∧ p2) ∨ (p5 ∨ True)))) := by
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
theorem thm_5_vars_787517419511143390955093955747 : (((p4 ∨ (False ∨ (((p3 → ((p4 ∧ True) → p1)) ∨ (p3 → p4)) → ((p3 ∧ (p4 ∨ (p2 ∨ True))) ∨ (p1 → ((p5 → p1) ∨ p1)))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



