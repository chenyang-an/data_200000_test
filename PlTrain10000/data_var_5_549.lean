variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9729279960662469865732507153 : ((((p5 → False) ∨ (((p1 → ((True ∧ (p3 ∧ True)) ∨ p5)) → (p1 ∧ ((p2 → False) → ((False ∧ p5) → (False ∧ p1))))) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_48389767748229252818657697856 : (((False → ((p5 ∧ (p1 ∨ (p4 ∨ ((p1 ∧ p3) → ((False → ((p5 → p1) ∨ True)) ∨ (False ∧ (False → p1))))))) → p2)) → (p2 ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318909699451301024626197570095 : (p4 ∨ ((p5 → ((p1 ∨ (True → p3)) → ((p3 → ((p3 ∧ p2) → (p4 ∧ ((p3 → True) → (True ∨ True))))) ∨ True))) ∨ (p5 ∧ (False ∨ p1)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147431334993793039781890835222 : (((((p1 ∨ p4) → False) → (((((p4 → (p1 ∧ False)) ∨ (p4 ∨ (p5 ∨ p2))) ∨ p2) ∧ p3) → p5)) ∨ p1) ∨ ((False → (False ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181384717048933387150710448271 : ((p1 ∨ (((p5 ∨ p5) ∨ p1) ∧ ((True → (True ∧ (p3 ∧ p3))) → True))) → ((p5 → ((p4 → (False ∨ p1)) ∧ (p1 ∧ p2))) → (p1 ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
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
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h8
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h10 := h2 h9
        -- We need to get the right conjuct of h10 based on <expert-advice>.
        let h11 := h10.right
        -- We need to get the left conjuct of h11 based on <expert-advice>.
        let h12 := h11.left
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h14
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319032948373223574309266721392 : (p4 ∨ ((((False ∧ ((((p1 ∧ p1) ∨ p5) ∨ ((p1 ∨ (p2 ∨ p1)) → (False ∨ p1))) → p2)) → False) → False) ∨ (False ∨ (True ∨ (p2 ∨ p5))))) := by
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
theorem thm_5_vars_260933487247694623360791676422 : ((p4 → False) → (p1 ∨ ((((True → ((True ∧ (False ∨ p5)) → ((p4 → p5) → p4))) ∧ (p2 ∨ p2)) ∨ ((False ∧ p1) ∧ p5)) ∨ (p2 → True)))) := by
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
theorem thm_5_vars_685720336153709124439212127457 : (((((p5 ∨ ((p4 ∧ (((True ∧ p2) ∨ (p4 ∧ False)) ∨ (False ∧ (p3 ∧ False)))) → p5)) ∨ p4) → ((((p4 ∧ p3) → p4) → p3) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9545364530276879836536640265 : (((((p2 ∨ p2) ∨ p4) → (((p2 ∨ p2) ∨ p4) → (((False ∧ (True ∨ False)) ∨ (((p3 ∧ p2) → p3) ∧ True)) ∧ (p5 → p5)))) ∨ p1) ∧ True) := by
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
      cases h1
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h7
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- One of the premise coincides with the conclusion.
          exact h8
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h11
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- One of the premise coincides with the conclusion.
          exact h12
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- One of the premise coincides with the conclusion.
        exact h16
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the left can always be decomposed.
          let h22 := h21.left
          let h23 := h21.right
          -- One of the premise coincides with the conclusion.
          exact h22
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h24 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Implications on the right can always be decomposed.
          intro h25
          -- Conjunctions on the left can always be decomposed.
          let h26 := h25.left
          let h27 := h25.right
          -- One of the premise coincides with the conclusion.
          exact h26
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h29
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- One of the premise coincides with the conclusion.
        exact h30
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h35
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- One of the premise coincides with the conclusion.
        exact h36
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h38 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h39
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- One of the premise coincides with the conclusion.
        exact h40
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h42 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h43
      -- Conjunctions on the left can always be decomposed.
      let h44 := h43.left
      let h45 := h43.right
      -- One of the premise coincides with the conclusion.
      exact h44
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h46
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h47 =>
    -- Disjunctions on the left can always be decomposed.
    cases h47
    case inl h48 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h49 =>
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h51 =>
          -- One of the premise coincides with the conclusion.
          exact h46
      case inr h52 =>
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h53 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h54 =>
        -- Disjunctions on the left can always be decomposed.
        cases h54
        case inl h55 =>
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h56 =>
          -- One of the premise coincides with the conclusion.
          exact h46
      case inr h57 =>
        -- One of the premise coincides with the conclusion.
        exact h46
  case inr h58 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h59 =>
      -- Disjunctions on the left can always be decomposed.
      cases h59
      case inl h60 =>
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h61 =>
        -- One of the premise coincides with the conclusion.
        exact h46
    case inr h62 =>
      -- One of the premise coincides with the conclusion.
      exact h46
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259037629761498715261992878480 : ((True → p4) → ((True → (False ∨ p1)) ∨ (p1 → ((((p3 ∨ (p4 ∨ (p3 ∧ p2))) → (p2 → p4)) → (p5 ∨ p5)) → ((p3 ∨ p2) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39740536302544819002425552990 : (((p5 ∨ (p2 ∨ (((((p5 → (True ∨ p5)) → p5) ∨ ((((p5 ∨ False) ∧ (p4 → p2)) ∧ True) ∧ p2)) → False) ∨ (True ∧ False)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197602760972223972564126965128 : (((p5 ∨ ((p5 → True) ∧ p5)) ∨ (p2 → False)) ∨ ((((p1 → p4) → ((p4 ∨ p3) ∨ p2)) ∨ (True → ((True → False) → p4))) ∨ (p2 ∧ True))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134301639394129443680204115127 : ((((False → p2) → ((p2 → (p5 ∨ ((((True ∧ p5) ∨ p3) ∧ p1) ∨ (((p3 → False) ∨ p4) → p1)))) ∧ p5)) ∨ True) ∨ (False ∧ (p3 → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113543633587629957109859828324 : (((((True ∧ p2) ∧ False) ∧ ((p4 ∧ p4) ∨ ((p2 ∨ False) ∨ ((((p1 → p1) ∧ p2) ∧ True) → (p2 → False))))) ∨ (p2 ∨ p4)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66680145471546304313721474894 : ((True → (((True → False) ∨ (p4 ∧ False)) ∨ (((True ∨ (p2 → p2)) ∧ (True ∨ False)) ∧ ((True ∧ ((p1 ∨ False) → (p5 ∧ p4))) ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65690892789044875978153665165 : ((p4 ∨ ((p3 ∧ (p1 ∨ (p4 → (p1 ∨ (((p1 ∧ (p4 ∧ p5)) ∧ p3) ∧ (p3 ∨ (p1 ∨ (False → (True → (p2 → p4)))))))))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90922039641420316626502969653 : (((True → False) ∧ ((p2 ∨ p3) ∨ (((((p5 ∧ ((p3 ∨ p3) ∨ p2)) ∨ (((False ∧ p3) → True) ∨ (p5 → p1))) ∨ p2) ∨ True) → p5))) → False) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h10 := h2 h9
      -- False on the left can always be used.
      apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160337762798442270668990951444 : (((False ∨ (p1 ∧ (((True ∨ p3) ∨ True) ∧ (((p3 → p2) → True) ∨ (False ∨ False))))) → (p2 ∨ p1)) → ((p2 ∧ (p5 ∨ (p4 ∧ p4))) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60294063344462792453071657801 : (((p1 → False) → (p1 → ((p1 ∧ ((p1 ∧ p4) ∨ (((((p4 → p5) ∧ p5) ∨ p2) ∨ (True ∨ p2)) → (False ∨ (p5 ∧ p3))))) ∨ p2))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167643310258557778553600450892 : ((((((p1 → p2) → p3) ∧ (p5 ∧ p4)) → ((True → (p4 → True)) → p5)) → (False ∨ p4)) → ((((p5 ∧ True) → True) ∨ p2) → (p3 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221933626304149619698787972221 : (((p5 ∧ p4) → p5) ∧ ((((False → p5) ∨ (p4 ∨ p4)) ∧ ((((False ∧ p3) → False) ∨ p2) → (p5 ∧ (p5 → (p2 ∧ p4))))) ∨ (p1 → p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57429080331275799924968536403 : (((p3 ∨ (p2 ∧ p4)) ∨ (((p1 → p2) → p1) ∨ (True ∨ (False → ((p5 ∧ (False ∨ ((p3 ∧ p1) → ((False ∨ p4) → p4)))) ∨ p5))))) ∨ False) := by
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
theorem thm_5_vars_312341343623508955010463194629 : (p2 ∨ (p2 → (p3 → (p5 → (((False ∨ False) ∧ ((p4 ∨ (p1 ∨ (True → p4))) ∧ (((p1 ∨ ((True ∨ p3) ∨ p2)) ∧ True) ∨ False))) ∨ p5))))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147901312951689193280420525488 : ((((((((False ∧ p1) → (p1 → p4)) ∧ p4) ∧ (p1 ∧ ((p5 → p2) → True))) ∨ True) → p5) ∧ (p4 ∧ p2)) ∨ ((p3 ∨ True) ∧ (False → p5))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695863365403279120029378708774 : (((((p3 → p5) ∧ ((p4 → (((p5 ∧ (p5 ∧ p3)) ∧ p5) ∨ True)) ∨ p5)) → ((p4 ∨ (False ∧ p2)) ∨ ((False → (p5 ∨ p4)) ∨ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185386413840353164678687465146 : ((p5 ∧ (True ∧ (p4 ∨ (((p1 ∧ (True → p1)) ∨ False) ∧ p3)))) ∨ ((False ∨ p4) ∨ (((p4 ∨ (False ∧ (True → (p4 ∧ True)))) → True) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42298879472637935194921991842 : (((p2 ∧ (((p1 → p2) → ((((p2 ∧ p5) ∨ (p5 → ((p5 ∧ (p2 ∨ (p2 → (p1 ∧ p2)))) ∧ p2))) ∨ True) ∨ p1)) → False)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319379787513516929560115665488 : (p4 ∨ ((p5 ∧ (p5 ∨ ((p3 ∧ p2) ∧ (p2 ∧ ((False ∧ p2) ∨ (p4 ∨ False)))))) ∨ ((False ∨ (p5 ∧ p4)) → (True ∨ (p5 ∧ (p3 ∧ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122732376440031041676062704300 : (((True ∧ ((True ∨ (((False → (((p4 → (p5 ∧ False)) ∧ p5) ∧ False)) → (p5 → (False → p1))) → p3)) ∨ p4)) → (p1 → True)) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44298835039578766479642388005 : ((((p2 ∧ ((p3 ∧ p2) ∧ ((p1 ∨ p5) ∧ (p4 ∨ ((p5 ∨ (p5 ∧ p2)) ∨ p4))))) ∧ ((False ∧ p2) → (p2 ∨ (True → p1)))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54255606677171134367082775272 : ((((p1 ∨ ((True ∨ p2) → p4)) ∨ (p2 ∧ p5)) ∧ ((p1 ∧ ((((p4 ∧ (p1 ∨ p5)) → p5) ∨ p5) → p1)) ∧ ((p4 ∧ p1) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148177934377626047933060394708 : ((((p2 → (((True ∨ p4) ∨ (((p4 → (p5 → p5)) ∧ p2) ∧ False)) ∧ p5)) → p5) ∧ ((p4 → p1) ∧ False)) ∨ ((False ∨ (p1 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309923476505712990928005527634 : (p2 ∨ (((p1 → (True → (True ∨ (((p3 → (p2 ∨ p5)) ∧ True) ∧ True)))) → ((p1 ∧ True) → p3)) ∨ ((p5 → p1) → ((True → True) ∨ True)))) := by
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
theorem thm_5_vars_304627769923039973847653712960 : (p1 ∨ (((p1 ∨ (False ∧ p4)) ∨ ((p4 ∧ p2) ∨ (True ∨ (((p2 ∨ p3) ∧ p4) → ((p5 → p4) → (p1 ∧ (False ∨ p4))))))) ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797803465561040633745680729673 : (((p1 → ((((((True ∨ p4) → p4) ∨ p3) ∧ p2) ∨ ((((p1 ∧ p3) → ((p3 ∧ False) ∧ (p3 ∨ p5))) ∨ False) ∨ p4)) ∧ (p5 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41172223766345950654695674812 : ((((((p1 ∨ (((p3 ∨ p2) → ((p3 ∨ (p2 → p5)) ∧ ((p2 ∨ p4) ∧ p2))) → p3)) → True) ∨ False) → ((True ∧ p3) ∨ p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187010734768681406788368909347 : (((True ∧ (p2 ∧ p3)) → (p2 → (((p1 → p3) → False) → p1))) → ((p3 → p2) ∨ ((((p3 → p4) ∨ (p2 → p5)) → (p5 ∨ True)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190027988292390749496141038044 : ((((True → ((p5 ∧ (p5 ∧ p5)) ∨ p1)) ∧ False) ∧ p2) ∨ (((p5 → True) ∨ (p4 → p4)) → (p4 ∨ ((True → p2) → (True ∨ (p4 → p4)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37396520173725920227672495732 : (((((True → (p4 → ((((True ∧ p2) ∨ ((p3 ∨ p5) → p5)) ∧ False) → (((True ∧ (p3 → True)) → True) ∧ p2)))) → p5) ∨ p1) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137973892533587396836886797874 : ((p5 ∨ (((p3 ∧ (False → True)) ∨ ((p4 → False) ∧ p3)) ∧ ((p1 ∨ p2) ∨ ((False → p1) ∧ ((p3 ∧ True) → p3))))) ∨ ((p5 ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51807070260506552586769502482 : (((p4 ∨ ((((p5 ∨ (p3 ∧ p3)) ∨ p2) ∧ ((True ∨ True) ∧ (True ∨ True))) → p2)) ∧ ((p5 ∨ (True ∧ (p3 ∨ True))) → (p1 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37842766856405652645060776765 : ((((p4 ∨ (p5 ∨ ((p1 → p4) ∧ ((True → (((p1 → (False ∧ p5)) ∨ (False ∨ p5)) → (p2 → (p1 ∨ p1)))) → False)))) → p1) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65326622482253905736721149126 : ((p3 ∨ ((((((p4 ∧ ((p2 ∨ p5) ∨ False)) → (p1 ∨ p4)) ∨ False) → (p3 ∨ (p2 ∨ p1))) ∨ p3) ∧ (((p1 → p3) ∧ p5) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60269466417624365179207950436 : (((False → p3) → ((p2 ∨ ((p5 ∧ (p3 ∧ p1)) ∨ p5)) → (((((p1 ∧ False) → (True → p4)) → p1) ∧ ((p4 ∧ False) ∨ p5)) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40296883097914194549701056673 : ((((p5 → (True → (((p5 → ((p1 → (True ∧ p4)) ∨ (p3 ∧ (True ∨ (p4 ∧ p3))))) → p5) → (p5 → (p4 ∨ p1))))) ∧ p5) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234365241434490261868256357780 : ((p1 → (p3 ∨ p3)) → (p2 → (((((True ∨ (p5 → p2)) ∨ ((p1 ∨ (p5 ∧ p5)) ∧ (False ∨ p1))) → p1) ∨ (True ∧ p2)) ∧ (False → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115337164034798818206669384705 : (((p1 ∨ (((p1 → ((p3 ∨ True) → p5)) ∧ p4) ∨ p3)) → (p5 ∧ (((((p5 ∧ True) ∨ False) → p5) → False) ∨ (True ∨ True)))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207882171281105084117233512325 : ((((False ∨ p1) → p2) ∧ (p5 → p1)) → (((p2 ∨ p4) ∨ (p5 ∨ ((((p4 ∧ True) → p5) → p4) ∨ (p3 ∧ False)))) ∨ (True ∧ (True ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135844771503617438823875655073 : (((p1 ∨ (False ∧ (((p3 ∨ True) → p5) → ((p2 ∧ p2) ∨ p4)))) ∧ ((p3 ∧ ((True ∨ (p2 ∧ True)) ∧ p4)) ∧ True)) ∨ (p4 ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_8200757631493556390695661612 : ((((p3 → ((((True ∧ p4) ∨ (((p5 ∧ (p1 → (p5 ∨ (p2 → False)))) ∨ p4) ∧ (p3 ∨ (p2 ∨ p5)))) ∧ p1) ∨ p5)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_213330788904667795249014850112 : (((p1 ∧ (p3 → p1)) ∧ p4) ∨ (p4 → ((p3 → p2) → (p3 ∨ (p4 → ((p5 → (p1 → (False → p3))) → ((p2 → False) ∨ (p4 ∨ p3)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340958410767663870595835134175 : (p2 → ((((False ∧ p1) → p1) → (((((p5 → ((True → p3) ∨ True)) ∧ (True ∨ p4)) ∨ (True ∧ p2)) → ((p2 ∨ p3) ∧ p5)) → p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54472534680299814769248764115 : ((((p1 ∧ ((p1 ∧ p2) ∧ p3)) ∧ (p1 ∨ False)) ∨ (((p5 ∧ True) ∧ p3) → ((p1 ∨ False) → ((p3 ∨ p1) ∨ ((False → True) ∨ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217555406811725020493351556399 : ((((p2 ∧ p2) ∨ p5) → p5) → ((p4 → (p5 ∧ (False ∧ (True → p4)))) → ((p1 → ((True ∧ p1) → p5)) ∨ (((p5 ∨ True) → p4) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38703072698378868781036244111 : (((((p5 ∧ p2) ∨ ((True ∨ False) ∧ p4)) ∨ ((((p2 ∧ ((True → p1) ∨ p1)) ∨ ((p3 → (p3 ∨ False)) → p5)) → False) → p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349645531009603867651045717716 : (p4 → (((((p2 → p5) ∨ p1) → ((p3 → ((((p1 → False) → (False ∨ p1)) ∨ (p4 ∨ (p5 → p3))) ∨ p5)) ∨ p4)) ∨ (False ∧ p1)) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322347959705483828624679379810 : (p5 ∨ ((((p3 ∧ ((p2 ∨ p2) ∨ ((((p1 ∨ p5) ∨ p2) ∨ (p4 ∨ ((True → p2) → p2))) ∧ True))) ∧ p5) ∧ ((False → p5) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61537576934005796177933269450 : ((p1 ∧ ((((p1 ∨ p3) → (p5 → ((p3 ∨ True) ∨ (False → p1)))) → p3) ∨ (((p1 → p5) ∧ (((p1 → False) → p2) → p3)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228062206379141001944657357427 : ((p4 ∧ (p2 ∧ p4)) ∨ (((p2 ∨ p4) ∧ (p4 → (p4 → False))) ∨ ((True ∨ (p3 ∧ (((p3 ∧ p2) ∧ False) ∨ ((p5 ∧ p4) ∧ True)))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115117980510572810892646751100 : (((((((p1 → False) ∧ (p3 → p1)) → p5) ∧ p5) ∨ (True ∧ p2)) → ((p1 ∧ ((True ∧ p5) ∧ True)) ∨ (p3 ∨ (p2 ∨ p5)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150011511393045724133894985446 : ((p5 ∨ ((p2 ∨ (((p2 ∧ ((p2 ∧ p1) → p1)) ∨ True) ∧ (True ∨ (p1 ∧ (p4 ∧ (False → p4)))))) → p2)) ∨ ((p2 ∨ p4) → (p2 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351640243531845748073053687920 : (p4 → ((((p4 → (p2 ∨ p1)) → p3) → ((p2 → p2) → ((False ∨ (p3 ∧ p5)) → p2))) ∨ ((p1 ∧ ((p1 ∧ p4) ∧ (p5 → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70847860481216019320699760648 : ((((p2 ∧ (True → (((True → ((p1 ∨ p5) ∧ p5)) → p2) ∧ False))) ∧ ((p3 ∨ (((p5 → p3) ∨ False) ∨ p1)) ∧ (True ∨ p4))) ∧ p4) → p5) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h16 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h22 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h24 := h7 h23
          -- We need to get the right conjuct of h24 based on <expert-advice>.
          let h25 := h24.right
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h27 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h28 := h7 h27
          -- We need to get the right conjuct of h28 based on <expert-advice>.
          let h29 := h28.right
          -- False on the left can always be used.
          apply False.elim h29
      case inr h30 =>
        -- False on the left can always be used.
        apply False.elim h30
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h32 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h34 := h7 h33
        -- We need to get the right conjuct of h34 based on <expert-advice>.
        let h35 := h34.right
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h37 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h38 := h7 h37
        -- We need to get the right conjuct of h38 based on <expert-advice>.
        let h39 := h38.right
        -- False on the left can always be used.
        apply False.elim h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640328451665110617557304852717 : (((((False → (True ∨ p2)) → (((False ∨ p2) ∧ (p4 ∧ False)) → ((True ∧ (p4 ∨ (p5 → True))) → (((True ∨ True) ∨ p3) ∨ p2)))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346575273544680324414774917477 : (p3 → ((p5 ∨ (((((True ∧ True) → p1) ∧ (((p2 ∨ True) → p4) ∧ p5)) ∧ ((True → (False → p3)) ∨ p4)) → p4)) ∧ ((p1 ∨ True) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h9 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h10 : (p2 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h11 := h7 h10
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h12
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780471048313073429388415850392 : (((p2 ∨ (((((True ∨ (True ∧ p4)) → p5) ∨ (True → True)) → ((True ∧ p1) → p4)) ∨ ((p2 ∧ False) → (((p4 ∧ False) ∨ True) ∨ p3)))) ∨ p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39138330192037329843002425819 : ((((p4 ∧ p2) → (p3 ∨ (((False → (p3 ∧ p2)) ∨ p4) → (p5 ∨ (False ∨ ((p5 → True) ∨ (((p1 → p4) → False) ∨ p2))))))) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64946125325996026115323369553 : ((p2 ∨ ((p2 ∨ ((p5 ∨ ((p3 ∨ p3) → (p5 ∧ p1))) ∧ p2)) ∧ (p1 ∨ (p5 ∧ (((p3 → ((p5 ∨ p4) → p4)) ∧ True) ∨ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37619398242379209277596349614 : (((((p3 ∨ (((p3 ∨ (p2 ∨ p4)) → (((False ∨ p2) ∧ (p5 → p1)) → p5)) → ((True ∨ False) → (True ∧ p2)))) ∧ p1) → p2) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68093567055511216527462666918 : ((p2 → (True → ((p5 ∨ (p2 → ((p4 ∨ ((p5 ∧ (p3 ∨ (p5 ∧ p1))) ∧ ((True → (p5 ∧ p5)) → (p4 ∧ p3)))) → p1))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732363555121979483839909234469 : ((((False ∧ p2) ∧ (((((p2 → False) ∧ p5) → ((p3 → (((False ∧ (p4 → p4)) ∨ p1) → False)) ∨ p4)) ∨ (p4 ∨ (p5 ∨ p5))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139094564293894534426042262216 : ((((((((False → True) ∧ p1) ∨ False) ∧ p3) ∨ (((p5 ∧ p3) → False) ∨ ((p3 ∧ p1) ∨ True))) → (p4 ∧ p2)) ∨ True) → (p2 ∨ (True ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349432405294432984106915876873 : (p3 → (p4 → (True ∧ ((p3 → (p5 ∧ (p2 ∧ p3))) → (((p2 → False) ∨ (p1 → ((p2 ∨ (p4 ∨ (p5 ∨ (p4 ∧ True)))) ∨ p1))) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856799119924337245381211785418 : (((((True ∧ ((p1 ∨ ((p5 ∨ (p2 ∨ (p4 ∨ False))) → ((((p4 → p3) ∨ (True ∨ (True ∨ p1))) ∧ False) ∧ p3))) → p5)) ∨ True) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ ((p1 ∨ ((p5 ∨ (p2 ∨ (p4 ∨ False))) → ((((p4 → p3) ∨ (True ∨ (True ∨ p1))) ∧ False) ∧ p3))) → p5)) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681027771613526284371393920818 : (((((True ∨ False) → (p2 → (((False → p5) ∨ (p5 → (((p5 → False) → (p2 ∧ True)) → False))) → False))) → ((p5 ∨ True) ∨ (p4 ∧ p1))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_222187090252521104420446612610 : (((p5 ∨ False) → p5) ∧ (p1 ∨ ((p4 → (p5 ∨ p2)) ∨ (((p1 → False) ∨ ((p2 ∨ ((p3 ∨ ((False → True) ∧ True)) ∨ p4)) ∧ p4)) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52850316581682883956449210762 : ((((False ∧ False) → (((p2 ∨ p3) ∧ (False → ((True ∧ p5) → False))) → p2)) → (((p3 → (True ∧ False)) ∧ (p3 ∨ (p4 ∧ p1))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152304431993181150514023747726 : ((((p3 ∧ (p4 ∨ p2)) ∧ p2) ∧ (((((p4 ∧ p5) ∨ (p2 ∨ p4)) ∧ (True → (p2 ∨ p5))) ∧ p5) ∨ True)) → (p2 → (p1 ∨ (p5 → p2)))) := by
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
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Conjunctions on the left can always be decomposed.
      let h13 := h11.left
      let h14 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h21
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h28.left
      let h31 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h35
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h38
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h39 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h40
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h41 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h42
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147732481016335454478888497863 : ((((True ∧ (True ∨ ((p3 ∨ p5) ∨ True))) → ((((True → (p5 ∨ True)) → False) → (False ∧ False)) → True)) → p4) ∨ ((p5 ∨ (True ∨ p4)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20550430349857101177914304826 : (((p3 → ((p5 ∨ (((False ∨ False) ∧ p5) → p2)) ∨ (p3 ∧ (False → False)))) → (p2 → (p4 → ((p1 → True) ∧ ((p2 ∨ p1) ∧ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164704296193501466496826631567 : (((((True ∧ p4) ∨ (p1 ∧ (((True ∨ ((p4 ∨ True) ∧ p5)) → False) ∧ p4))) ∨ True) ∨ p1) ∨ ((p4 ∧ ((p4 ∧ p2) ∨ (False ∧ p5))) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_109309311373590904791055050773 : ((p1 ∨ ((p2 ∧ ((True → False) ∧ (p3 → ((p5 → p2) ∨ ((((False → ((p5 ∧ p4) ∧ p1)) ∨ True) → p2) ∨ False))))) → False)) ∧ (True ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64171264361161769371060154899 : ((False ∨ ((p2 ∨ p1) ∨ ((p2 ∨ (p4 ∨ ((((p3 ∨ p2) ∨ p5) ∧ (p4 ∨ p4)) ∨ p3))) → ((p3 → p2) ∨ ((p1 → p4) ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260013164094311619800099665671 : ((p2 → True) → ((p1 → p4) ∨ ((p5 → ((p3 ∧ ((False ∧ ((p4 ∨ False) ∨ (p4 ∨ (True → True)))) ∧ p1)) ∨ ((True ∨ False) ∧ True))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
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
theorem thm_5_vars_213541543531585386460257622659 : ((((p1 ∧ p5) ∧ p5) ∨ p4) ∨ (p5 → (((p2 ∨ p3) → p1) ∨ ((p5 → True) ∨ ((False ∨ (p3 ∨ (p3 ∧ ((False → True) ∨ p4)))) ∨ True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264160013469640855507776416501 : (True ∧ (((False → (p4 → ((False ∧ p2) ∧ p3))) → p5) ∨ (((p5 ∨ False) ∨ ((False ∨ (False ∨ p3)) ∧ p4)) → ((p5 ∨ (p2 ∧ True)) ∨ p3)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205079585663348288676491895999 : (((p5 → (True ∧ (True ∧ p2))) → p5) ∨ (((((p2 → False) → ((p5 → ((p1 ∨ (p5 ∧ False)) → (p3 → p2))) ∧ p4)) → True) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110902546855818718522213564988 : (((((p4 ∨ False) ∨ ((p5 ∧ ((p2 ∧ p2) → p4)) ∨ ((((p1 ∨ p5) ∨ (p5 ∧ True)) ∨ (p5 → p1)) ∨ False))) → p4) ∧ p4) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52697209856986725039379390090 : (((p1 → (p1 → (p5 ∧ (False ∨ ((p5 → ((p5 ∨ p1) → p1)) ∨ p3))))) ∨ (((p2 → ((p4 ∨ (p5 → True)) → p3)) ∨ p2) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_7981515841467935338245702329 : (((((p3 ∧ (((p2 ∨ p4) ∨ (p2 ∨ (((((p4 ∨ p5) ∧ p2) ∧ ((True ∧ p5) → p1)) → p4) ∨ p3))) → p4)) ∨ True) ∨ False) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_172998405398830123434230060573 : ((p5 ∧ ((p5 ∧ (True ∨ (p5 → (p1 ∧ True)))) ∧ (p2 ∧ (p5 ∧ (p4 ∨ p2))))) ∨ (((p3 ∨ (p3 ∧ p5)) → p5) ∨ ((False → True) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790254567591193881393547964816 : (((p5 ∨ (p1 ∧ (((p5 → False) ∨ (((p1 ∨ p4) ∨ True) ∨ (p5 ∧ (True ∨ p5)))) ∧ ((p2 ∧ (p1 ∧ (True ∧ (p5 ∧ p1)))) → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_936703756366356830798605746584 : ((((((p1 ∧ (p4 → False)) → True) ∨ p4) ∧ (((((True ∨ (p5 ∨ (True ∧ p2))) ∨ False) ∧ (True ∨ p4)) → (p2 ∨ (True → True))) → p3)) → p3) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((((True ∨ (p5 ∨ (True ∧ p2))) ∨ False) ∧ (True ∨ p4)) → (p2 ∨ (True → True))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h11 =>
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
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h8
            case inl h17 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h18
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h19 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h20
              -- True on the right can always be proven directly.
              apply True.intro
          case inr h21 =>
            -- Conjunctions on the left can always be decomposed.
            let h22 := h21.left
            let h23 := h21.right
            -- Disjunctions on the left can always be decomposed.
            cases h8
            case inl h24 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h23
            case inr h25 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h23
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h26
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h27 := h3 h5
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h28 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h29 : ((((True ∨ (p5 ∨ (True ∧ p2))) ∨ False) ∧ (True ∨ p4)) → (p2 ∨ (True → True))) := by
      -- Implications on the right can always be decomposed.
      intro h30
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h35 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h36
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h37 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h38
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h32
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
            -- Conjunctions on the left can always be decomposed.
            let h46 := h45.left
            let h47 := h45.right
            -- Disjunctions on the left can always be decomposed.
            cases h32
            case inl h48 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h47
            case inr h49 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h47
      case inr h50 =>
        -- False on the left can always be used.
        apply False.elim h50
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h51 := h3 h29
    -- One of the premise coincides with the conclusion.
    exact h51
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63226378564585785775176871158 : ((p5 ∧ (((p2 ∨ (p3 → (p3 ∨ p4))) → ((p4 ∨ p5) ∧ (p3 → (p3 ∧ p3)))) ∧ (((p5 ∨ True) → p3) → ((p4 → p3) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134148407713696450324284984887 : ((((((p4 → ((((False ∧ p2) → p4) ∧ False) ∨ (p1 ∨ (p3 ∨ p1)))) ∨ p1) ∧ p4) ∨ ((p1 ∧ True) ∨ p2)) ∨ p1) ∨ ((p2 ∨ p2) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140600317495802764407855064560 : ((((p5 ∧ ((p3 ∨ p5) ∧ ((((p5 ∧ p3) → p4) ∧ p2) → p1))) ∧ (p5 ∧ p1)) → ((p5 ∧ (True → p3)) → p4)) → (p4 ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341007748298229906294654501997 : (p2 → ((p1 ∧ ((p4 ∧ (((((p5 ∨ p4) ∨ (p3 ∨ p3)) ∧ p2) ∧ p2) → (p5 ∧ (p2 ∧ (p4 ∨ ((p5 ∨ p4) → p5)))))) ∨ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696418206869732030175848489987 : (((((((p2 ∨ (p1 → (p4 → (p2 → p1)))) ∨ p4) ∨ p2) ∧ False) ∧ (p2 ∨ ((((p3 → p5) → ((True → p1) ∧ False)) ∨ p1) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16589387475772692514862966037 : ((((p5 ∧ ((((((p3 ∨ (p3 ∧ p3)) → p1) ∧ (p2 ∨ True)) ∨ (p2 ∧ p1)) → (p2 ∧ True)) → p2)) ∧ False) ∨ (True ∨ (False → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227702336601251565999643842069 : ((p1 ∧ (p1 ∧ p4)) ∨ ((True → ((False → (p5 → p1)) → p4)) → ((p4 ∨ ((True ∨ ((p1 ∧ p5) ∧ True)) ∧ (True ∧ (p4 ∨ True)))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



