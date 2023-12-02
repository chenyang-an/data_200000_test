variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136322306999126069555936829028 : ((((True → (True ∧ p5)) → False) ∧ (p2 → ((p3 ∧ (p5 ∧ ((p5 ∧ p1) ∨ (p1 → p5)))) ∨ ((p3 ∨ False) → p1)))) ∨ ((p2 ∧ True) → p2)) := by
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
theorem thm_5_vars_323469963315386859180695474329 : (p5 ∨ ((((p4 ∨ ((p4 ∨ ((True ∨ False) ∧ p2)) ∨ (True ∨ p3))) → (((p3 → p5) → p1) → (True → p2))) ∧ p5) ∨ (p3 ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_112471580646526025356806061179 : (((((p5 ∨ (p1 ∨ (p4 ∨ p3))) → ((p2 ∨ (p4 → (p3 ∧ p2))) ∨ (((False ∨ p5) ∨ (p1 → True)) ∧ p5))) ∨ p1) → p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45477670913958620193031618079 : (((False ∨ (((p5 ∨ p4) ∧ ((p1 ∨ p1) ∨ (p5 → (True → (((p1 → p1) ∧ False) ∨ p5))))) ∧ (p4 → ((False ∧ p5) ∧ False)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217325576702429376578659316196 : (((False ∨ (True ∨ True)) ∨ p2) → (((False ∧ (p3 → p1)) ∨ p2) ∨ (False → ((True ∨ (False → (p3 ∧ (p3 ∨ (p4 ∨ False))))) → (p4 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Implications on the right can always be decomposed.
        intro h7
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- False on the left can always be used.
          apply False.elim h6
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h6
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- False on the left can always be used.
          apply False.elim h11
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h11
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114870092944834487741354735265 : ((((True → ((p3 ∨ False) ∧ (False → p2))) → (p5 ∧ ((p5 ∨ True) → p4))) ∨ ((True ∨ p4) → (False → ((p1 ∧ p1) ∧ True)))) ∨ (True ∧ p4)) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330490267891144174880141301271 : (True → (p4 ∨ (((p3 ∧ p2) ∨ (False ∨ (((p3 ∨ True) ∨ (((False ∨ p5) → p4) ∨ p3)) ∧ ((True ∨ p4) → (p3 ∨ True))))) ∨ (p1 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_219115592315197792985314958720 : ((True ∨ ((False → p4) → p1)) → (((p4 ∨ (p4 → p4)) ∨ False) → (p1 ∨ ((False ∧ p2) ∨ ((((p1 → p4) ∧ p2) ∧ (p2 ∧ p1)) → p4))))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
        have h14 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h13, we can now drive its conclusion.
        let h16 := h13 h14
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- Conjunctions on the left can always be decomposed.
        let h22 := h20.left
        let h23 := h20.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h21.left
        let h25 := h21.right
        -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
        have h26 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h22, we can now drive its conclusion.
        let h27 := h22 h26
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
        have h29 : (False → p4) := by
          -- Implications on the right can always be decomposed.
          intro h30
          -- False on the left can always be used.
          apply False.elim h30
        -- We have shown the premise of h28, we can now drive its conclusion.
        let h31 := h28 h29
        -- One of the premise coincides with the conclusion.
        exact h31
  case inr h32 =>
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47551792779866213405344996106 : (((True → ((((((True ∨ p2) → (p3 ∧ (p2 ∧ p3))) ∨ p4) ∨ p3) ∨ ((False ∨ p3) ∨ (False ∧ (p1 → True)))) → False)) ∨ (p2 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187361069854251375604623797002 : ((p3 ∧ ((((p1 → p1) → (p5 ∧ False)) → (p5 ∧ False)) → p5)) → ((False ∧ (p4 → p3)) ∨ ((p5 ∧ ((True ∨ False) → (p5 ∨ p4))) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p1 → p1) → (p5 ∧ False)) → (p5 ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h10 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h14 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h14
  -- Implications on the right can always be decomposed.
  intro h15
  -- Disjunctions on the left can always be decomposed.
  cases h15
  case inl h16 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : (((p1 → p1) → (p5 ∧ False)) → (p5 ∧ False)) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h19
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- One of the premise coincides with the conclusion.
      exact h22
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h23 : (p1 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h25 := h18 h23
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h27 := h3 h17
    -- One of the premise coincides with the conclusion.
    exact h27
  case inr h28 =>
    -- False on the left can always be used.
    apply False.elim h28
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h29 : (((p1 → p1) → (p5 ∧ False)) → (p5 ∧ False)) := by
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h31 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h32
      -- One of the premise coincides with the conclusion.
      exact h32
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h33 := h30 h31
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- One of the premise coincides with the conclusion.
    exact h34
    -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
    have h35 : (p1 → p1) := by
      -- Implications on the right can always be decomposed.
      intro h36
      -- One of the premise coincides with the conclusion.
      exact h36
    -- We have shown the premise of h30, we can now drive its conclusion.
    let h37 := h30 h35
    -- We need to get the right conjuct of h37 based on <expert-advice>.
    let h38 := h37.right
    -- False on the left can always be used.
    apply False.elim h38
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h39 := h3 h29
  -- One of the premise coincides with the conclusion.
  exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187585208948269343720377790631 : ((p3 ∨ (p2 ∧ ((p4 ∨ ((p2 → True) ∨ (False → p1))) ∧ p2))) → (True ∧ (((((p5 → True) → p4) → p3) ∨ (p2 → (True ∧ p4))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923596293314354578913324754088 : (((((True ∨ (((p1 → True) ∧ p4) ∧ False)) → ((p5 ∧ p4) ∧ p3)) ∧ (p5 ∨ ((p4 → (p4 ∧ (True ∧ (p4 ∧ p3)))) → (False → p2)))) → p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (((p1 → True) ∧ p4) ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252653167822128758581809516216 : ((p5 → p4) ∨ ((p3 ∧ ((p2 → p4) ∨ ((((p4 ∨ False) → p2) ∧ p3) → p3))) → ((p5 ∧ ((p3 ∧ p3) ∧ p3)) ∨ ((p1 ∧ p4) ∨ p3)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133904705546371178545042257589 : (((p2 ∨ (((p5 ∨ (p4 → p4)) → ((((p3 ∨ True) ∧ p5) → ((False ∧ (p4 ∨ p4)) ∨ False)) ∧ p5)) ∧ p3)) ∧ p1) ∨ (p2 ∨ (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244098230018058651856433177379 : ((True ∧ p3) ∨ ((p4 → (p4 ∧ False)) ∨ ((p3 ∧ (((((p1 ∧ p1) → False) → False) → ((p4 ∧ ((p4 → False) → p4)) → p5)) ∨ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124265869363797426091774045801 : (((p2 ∨ ((p2 ∧ p1) → ((True ∨ p3) → (p5 → p2)))) → (((p2 ∨ p2) → (True ∧ (False ∨ (True ∨ (p1 ∧ p2))))) → False)) → (p5 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ ((p2 ∧ p1) → ((True ∨ p3) → (p5 → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h3.left
      let h8 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- One of the premise coincides with the conclusion.
      exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h2
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : ((p2 ∨ p2) → (True ∧ (False ∨ (True ∨ (p1 ∧ p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h17 := h12 h13
  -- False on the left can always be used.
  apply False.elim h17
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h18 : (p2 ∨ ((p2 ∧ p1) → ((True ∨ p3) → (p5 → p2)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Implications on the right can always be decomposed.
    intro h21
    -- Disjunctions on the left can always be decomposed.
    cases h20
    case inl h22 =>
      -- Conjunctions on the left can always be decomposed.
      let h23 := h19.left
      let h24 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h23
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h19.left
      let h27 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h26
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h28 := h1 h18
  -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
  have h29 : ((p2 ∨ p2) → (True ∧ (False ∨ (True ∨ (p1 ∧ p2))))) := by
    -- Implications on the right can always be decomposed.
    intro h30
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Disjunctions on the left can always be decomposed.
    cases h30
    case inl h31 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h32 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h28, we can now drive its conclusion.
  let h33 := h28 h29
  -- False on the left can always be used.
  apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63385922147189557730166939818 : ((p5 ∧ (False ∨ ((p5 ∨ (False ∧ (p3 ∨ p2))) ∨ (((((p5 → p2) ∧ ((False → ((p3 ∧ p2) ∧ p1)) ∧ p2)) ∧ p5) ∧ p3) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84749339448671684478322107398 : ((((((p4 ∨ (p5 ∨ p3)) ∨ True) ∨ p5) ∨ (p4 → ((p1 ∧ p5) → p3))) ∧ (((p1 → False) ∧ p1) ∧ ((p1 → p5) ∧ (p1 ∨ p1)))) → p4) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h3.left
          let h9 := h3.right
          -- Conjunctions on the left can always be decomposed.
          let h10 := h8.left
          let h11 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h9.left
          let h13 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h15 =>
            -- One of the premise coincides with the conclusion.
            exact h7
        case inr h16 =>
          -- Disjunctions on the left can always be decomposed.
          cases h16
          case inl h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h3.left
            let h19 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h20 := h18.left
            let h21 := h18.right
            -- Conjunctions on the left can always be decomposed.
            let h22 := h19.left
            let h23 := h19.right
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
              have h25 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h24
              -- We have shown the premise of h20, we can now drive its conclusion.
              let h26 := h20 h25
              -- False on the left can always be used.
              apply False.elim h26
            case inr h27 =>
              -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
              have h28 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h27
              -- We have shown the premise of h20, we can now drive its conclusion.
              let h29 := h20 h28
              -- False on the left can always be used.
              apply False.elim h29
          case inr h30 =>
            -- Conjunctions on the left can always be decomposed.
            let h31 := h3.left
            let h32 := h3.right
            -- Conjunctions on the left can always be decomposed.
            let h33 := h31.left
            let h34 := h31.right
            -- Conjunctions on the left can always be decomposed.
            let h35 := h32.left
            let h36 := h32.right
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
              have h38 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h37
              -- We have shown the premise of h33, we can now drive its conclusion.
              let h39 := h33 h38
              -- False on the left can always be used.
              apply False.elim h39
            case inr h40 =>
              -- We want to use the implication h33 based on <expert-advice>. So we show its premise.
              have h41 : p1 := by
                -- One of the premise coincides with the conclusion.
                exact h40
              -- We have shown the premise of h33, we can now drive its conclusion.
              let h42 := h33 h41
              -- False on the left can always be used.
              apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h3.left
        let h45 := h3.right
        -- Conjunctions on the left can always be decomposed.
        let h46 := h44.left
        let h47 := h44.right
        -- Conjunctions on the left can always be decomposed.
        let h48 := h45.left
        let h49 := h45.right
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h50 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h51 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h50
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h52 := h46 h51
          -- False on the left can always be used.
          apply False.elim h52
        case inr h53 =>
          -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
          have h54 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h53
          -- We have shown the premise of h46, we can now drive its conclusion.
          let h55 := h46 h54
          -- False on the left can always be used.
          apply False.elim h55
    case inr h56 =>
      -- Conjunctions on the left can always be decomposed.
      let h57 := h3.left
      let h58 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h59 := h57.left
      let h60 := h57.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h58.left
      let h62 := h58.right
      -- Disjunctions on the left can always be decomposed.
      cases h62
      case inl h63 =>
        -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
        have h64 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h63
        -- We have shown the premise of h59, we can now drive its conclusion.
        let h65 := h59 h64
        -- False on the left can always be used.
        apply False.elim h65
      case inr h66 =>
        -- We want to use the implication h59 based on <expert-advice>. So we show its premise.
        have h67 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h66
        -- We have shown the premise of h59, we can now drive its conclusion.
        let h68 := h59 h67
        -- False on the left can always be used.
        apply False.elim h68
  case inr h69 =>
    -- Conjunctions on the left can always be decomposed.
    let h70 := h3.left
    let h71 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h72 := h70.left
    let h73 := h70.right
    -- Conjunctions on the left can always be decomposed.
    let h74 := h71.left
    let h75 := h71.right
    -- Disjunctions on the left can always be decomposed.
    cases h75
    case inl h76 =>
      -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
      have h77 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h76
      -- We have shown the premise of h72, we can now drive its conclusion.
      let h78 := h72 h77
      -- False on the left can always be used.
      apply False.elim h78
    case inr h79 =>
      -- We want to use the implication h72 based on <expert-advice>. So we show its premise.
      have h80 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h79
      -- We have shown the premise of h72, we can now drive its conclusion.
      let h81 := h72 h80
      -- False on the left can always be used.
      apply False.elim h81



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134920628569426248281130968637 : ((((p2 ∧ (p4 ∨ (True ∧ (((p3 ∧ (False → p5)) ∨ (p1 ∧ (p5 ∧ (p5 → p1)))) → p2)))) ∨ p5) ∧ (p5 → True)) ∨ (p1 ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115373033726996006419297060862 : ((((p5 ∨ ((p4 → p5) ∧ p3)) ∧ (p5 ∧ p4)) ∧ ((p2 → (True ∨ ((p2 → p1) ∨ p5))) ∧ ((True ∨ True) ∨ (p3 ∨ p4)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186732582320798544863744484982 : (((p2 → ((p2 ∨ False) ∧ (True ∧ p5))) ∨ (p3 → (p5 ∧ p1))) → (p2 ∨ (p2 → (p1 → ((p1 → False) ∨ (True ∧ ((p2 ∨ p4) ∧ p2))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217214970430976963869226852454 : ((((False → p5) → p1) ∨ False) → (p2 ∨ (p5 ∨ (((p4 ∨ ((p2 ∧ (p3 ∨ True)) ∨ (True → ((True ∧ False) → False)))) ∨ (True → True)) ∨ p5)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621883776655570560424709380405 : ((((p1 ∧ (((False ∨ p2) ∨ p4) → ((True ∨ p5) ∧ (p3 ∧ (p1 ∨ (p1 ∨ ((((p4 → p1) ∧ p2) ∨ (p5 ∧ False)) → p3))))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_193760146800364507155192832304 : ((p3 ∧ (True ∧ ((p1 ∨ (p3 ∧ (p5 ∧ True))) ∨ p3))) → ((p5 ∨ (p2 ∧ p5)) ∨ ((False ∧ False) → (p5 ∧ (p1 ∨ (True ∨ (p1 ∧ p4))))))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
      -- Conjunctions on the left can always be decomposed.
      let h11 := h8.left
      let h12 := h8.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h16
  case inr h18 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
    -- Conjunctions on the left can always be decomposed.
    let h22 := h19.left
    let h23 := h19.right
    -- False on the left can always be used.
    apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57809535939747639282907024995 : (((p2 ∧ (True → p4)) → ((((p4 ∨ p4) → ((p4 → p4) ∧ False)) → (p2 ∧ ((False ∨ (((p1 → p3) → p4) → p5)) ∧ p1))) ∧ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h7
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h14 : (p4 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
    have h15 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h13, we can now drive its conclusion.
    let h16 := h13 h15
    -- One of the premise coincides with the conclusion.
    exact h16
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h17 := h2 h14
  -- We need to get the right conjuct of h17 based on <expert-advice>.
  let h18 := h17.right
  -- False on the left can always be used.
  apply False.elim h18
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213199149544759691297884658087 : ((((True → p4) ∨ p3) ∧ True) ∨ (((p4 → False) ∨ ((p4 → p3) → True)) ∧ (p4 ∨ ((False ∨ p4) ∨ (((p4 ∧ (p2 ∧ p3)) ∧ True) ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263132464171987575285346198621 : (True ∧ (((True ∨ ((True ∧ p1) → p4)) ∧ (p5 ∧ (p5 → (((True ∧ ((p5 → (p3 ∨ (False ∨ p5))) → p1)) ∧ p1) ∧ p4)))) ∨ (p4 → p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114416855176064143080311569809 : ((((p5 → True) ∧ ((p2 → p1) ∧ (((p3 ∨ p2) → (p1 ∨ ((p2 → p1) → p4))) ∧ p5))) ∨ (False ∨ (False → (p4 → True)))) ∨ (p1 ∨ p4)) := by
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
theorem thm_5_vars_178431840470526781924753906239 : ((((p5 ∨ (p3 ∧ ((False → p5) → p2))) ∧ p3) ∧ ((p3 → p2) ∧ p2)) ∨ (((p2 ∨ p5) ∨ (((p4 ∨ p3) ∨ p3) → (True → True))) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134209682911365717734978702119 : (((((True ∨ ((True → (p5 → False)) ∧ True)) → p1) ∨ (((p2 → (p1 → ((p1 ∧ p3) ∨ p3))) → p5) ∨ True)) ∨ p5) ∨ (True ∧ (p1 → p1))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262477731830517777532180007968 : (True ∧ ((p5 ∨ (((p5 → True) ∧ (p3 ∧ ((p2 → ((p3 → ((True → (p1 ∨ p4)) ∨ (p5 ∨ False))) ∨ p1)) → (p5 → p3)))) ∨ p2)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134068062621540663603279721795 : (((((False → ((p3 ∧ ((p1 ∧ (p3 ∨ False)) → p5)) ∧ (((p1 → p4) → (p5 ∧ p5)) → p5))) ∨ p3) → p4) ∨ True) ∨ (p1 ∨ (p5 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114921361008443765956287312760 : (((((p2 → True) ∨ ((True → p1) ∧ (p2 → (p2 ∨ (False ∧ True))))) → p1) → (False ∧ ((p5 → p3) ∨ (p2 ∨ (False ∧ False))))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124262415631326371673379490167 : (((True ∨ (((((False ∧ p5) → True) ∨ False) ∨ p4) ∧ p5)) → (((p3 ∨ ((p3 ∨ p4) ∨ p5)) ∨ (True ∧ (False → False))) → p5)) → (p4 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (((((False ∧ p5) → True) ∨ False) ∨ p4) ∧ p5)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∨ ((p3 ∨ p4) ∨ p5)) ∨ (True ∧ (False → False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133540901482286989205774854920 : (((((p2 → p1) → (((p5 ∨ ((p5 → p4) ∨ p4)) → ((((False ∧ True) → True) ∧ p3) ∨ p1)) → False)) ∧ p3) ∧ p2) ∨ (False → (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252451416465776814176644703007 : ((p5 → p1) ∨ ((p5 ∨ ((p1 → p3) → ((((p3 ∧ (p4 → (p4 ∧ True))) ∨ p4) → (False ∧ ((False ∨ (p1 ∧ p5)) ∧ False))) ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616887138077554509599761486950 : (((((((p2 ∨ (p2 ∨ p2)) ∧ p5) ∧ ((True ∨ p3) ∧ True)) → (((p4 → p2) ∧ p1) ∨ (((p3 → (p5 ∧ p4)) ∧ p2) ∨ p1))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_118219060503890213174146521933 : ((p1 ∨ (((p4 ∨ ((p3 ∧ ((p3 → (p2 → p4)) ∨ ((p1 ∨ (p3 ∧ True)) ∧ p1))) ∧ (p1 ∧ (True ∨ p2)))) ∨ True) ∨ p2)) ∨ (p3 ∨ p5)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61012097056827922682518456580 : ((False ∧ (((p4 → p3) → (p4 → (((p2 → p2) ∧ p3) ∨ (((p2 ∨ ((p3 → (p5 ∨ True)) → p3)) → (p4 ∧ p3)) ∧ True)))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55619910468779449005912541293 : (((p3 → (p1 ∧ (p2 ∧ (False ∧ p3)))) → ((p5 → (p3 → (p5 ∧ (((p1 → (p5 → p3)) ∧ ((p1 ∨ p4) → True)) → p1)))) ∨ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158281223146640986140118037487 : (((p5 → (p4 ∧ p5)) ∨ (p4 → (((p2 → (p5 → (p1 → False))) ∨ True) → (p3 ∧ (p4 ∨ p4))))) ∨ ((((True ∨ p1) ∧ False) ∧ True) → False)) := by
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_810352964515689896763343135261 : (((p5 → ((((p4 ∨ (True ∧ True)) ∨ (p1 → (True ∧ p3))) → p1) ∨ (False → (p5 → (((p2 ∨ p3) ∨ (p3 → p5)) ∨ (True ∧ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585693547880699625715008385466 : (((((((p3 ∨ ((p1 ∧ ((((p5 ∧ (False ∧ (p2 ∨ False))) ∧ (p2 ∧ (p1 → p5))) ∧ p2) → p3)) ∧ p3)) → False) → p4) ∧ p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188994284679417999326966527463 : ((((p5 ∨ False) ∧ p1) ∨ (p3 → (p3 ∨ (p3 ∨ p4)))) ∧ ((((((True → p4) ∧ p3) ∨ ((p2 ∨ p2) ∧ p2)) ∧ (p3 ∨ p3)) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205124274137781278943082046693 : ((((p4 → True) ∨ p1) ∧ (p4 ∧ p3)) ∨ ((True ∨ ((p2 ∨ (p2 → True)) ∨ False)) → (p2 ∨ (p2 → (p4 → (p1 ∨ ((False ∧ p5) ∨ p2))))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Implications on the right can always be decomposed.
        intro h10
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264149801612177291578869790698 : (True ∧ ((((p4 ∧ ((p2 ∧ True) ∧ True)) ∧ False) ∧ False) ∨ (p2 → ((p1 ∨ False) → (((((True ∧ p5) ∨ p5) ∧ p4) ∧ True) ∨ (True ∧ p1)))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264436690341482083429041913729 : (True ∧ (((True ∨ (p4 ∨ p1)) → True) → (((p2 ∧ (p2 → ((p3 ∨ p4) ∧ False))) ∧ (p3 ∨ p5)) ∨ (((p5 → (p4 ∧ p1)) → p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191301592386888630559955270310 : (((p2 → p1) ∧ ((False ∨ ((p4 ∧ True) ∧ True)) → False)) ∨ ((((False → p1) ∨ p3) ∨ False) → ((True → ((p2 → p4) ∨ (p1 → p1))) ∨ p4))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682322133152182461636370717450 : ((((((False ∨ (False ∨ (((p5 ∧ True) → p5) → (p1 ∨ False)))) ∧ (p2 ∧ p1)) ∨ (p4 ∧ p3)) ∧ (((False → (p3 ∨ False)) ∧ p3) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713280590856215563160311134131 : ((((p4 ∨ ((p2 → p4) ∨ (True ∧ p2))) ∨ ((p3 ∧ (p3 ∧ ((p3 → True) → ((p5 ∨ ((p1 → p3) ∧ p5)) ∧ p1)))) ∨ (False → p4))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159804343074827574838786787966 : (((p4 ∧ (((((False ∨ False) → p1) ∨ (p5 ∨ ((p1 ∨ False) ∧ p4))) ∨ (p3 → p1)) ∧ p1)) ∨ False) → ((False ∨ (p4 → p2)) ∨ (p2 → p4))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h17
            -- One of the premise coincides with the conclusion.
            exact h15
          case inr h18 =>
            -- False on the left can always be used.
            apply False.elim h18
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h21 =>
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765078829762563007720854485450 : (((p4 ∧ (((p1 ∨ p2) ∧ (((((p2 → ((p1 ∧ False) → (p1 → (p5 ∧ p1)))) ∨ p1) ∧ True) ∨ p4) → (p3 ∧ True))) ∧ (p5 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318596419670573713961832298810 : (p4 ∨ ((((((((p2 → p3) → p4) ∨ (False ∨ True)) ∧ p3) → p4) ∧ p2) ∧ (False → (((True ∧ p3) → (p5 → p2)) ∧ False))) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45474917502125986805373253405 : (((False ∨ ((((p3 → (((p3 ∧ (False ∨ True)) → False) ∧ p5)) ∧ (p2 ∨ (p1 → (p4 ∨ True)))) ∨ (p1 ∨ p4)) → (p5 ∧ p5))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134010471335952833441740460269 : ((((p2 ∨ (p5 ∨ (((((True ∨ p1) → p1) ∧ (p5 → (True ∨ p5))) → p3) → (p3 ∧ (False ∨ p3))))) ∧ p1) ∨ True) ∨ ((p1 ∧ p1) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205152058800010068096682428397 : (((False ∧ (p4 ∧ p3)) ∧ (p4 ∨ True)) ∨ (((((True → (p1 ∨ False)) ∧ (p4 ∨ p5)) ∧ (False → p2)) ∨ (False ∧ (p3 ∨ p2))) ∨ (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603980574550693845378849590692 : ((((p5 ∨ (((p5 ∨ True) → ((((p1 ∧ p3) ∨ False) ∨ ((False → (True ∧ p2)) → True)) → ((p3 ∨ True) → (p4 ∧ False)))) → p5)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43698673833395278648551598326 : (((((((p1 ∧ (p3 ∨ p2)) ∧ p2) ∧ p1) ∨ ((((False ∧ (p2 → p5)) ∧ p1) ∧ p3) ∧ (p5 → (p5 ∧ (p1 ∧ p3))))) → p5) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141031962644068216073585507324 : ((((p3 ∨ p5) ∨ (((False ∧ p5) → True) → p5)) ∧ (((False ∨ p1) ∧ ((False ∧ p4) ∨ p4)) ∨ (True → (p4 ∨ False)))) → ((p1 ∨ p3) ∨ True)) := by
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
      cases h3
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- False on the left can always be used.
          apply False.elim h9
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h11 =>
            -- Conjunctions on the left can always be decomposed.
            let h12 := h11.left
            let h13 := h11.right
            -- False on the left can always be used.
            apply False.elim h12
          case inr h14 =>
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h19
          case inl h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- False on the left can always be used.
            apply False.elim h23
          case inr h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h26 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h31 =>
        -- False on the left can always be used.
        apply False.elim h31
      case inr h32 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h33 =>
          -- Conjunctions on the left can always be decomposed.
          let h34 := h33.left
          let h35 := h33.right
          -- False on the left can always be used.
          apply False.elim h34
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h37 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68186117744807758448821180773 : ((p3 → (((((p4 → p4) → (p4 → ((True ∧ (p2 ∧ ((True ∨ (False → True)) → False))) ∧ p2))) ∨ True) ∨ (p4 → (p1 → p3))) ∨ p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_55567760151864926910973469343 : (((p5 ∧ (p2 → ((p3 ∨ p5) ∨ p1))) → (((p2 ∧ (((p1 → True) ∨ p3) ∧ p5)) → p1) ∨ ((((False ∧ p3) → False) ∨ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156731745991524282899947112571 : (((((p5 ∧ (p1 ∨ p2)) ∧ p1) ∧ ((True → (True ∧ (p4 → ((p4 → p4) ∨ p4)))) ∨ True)) ∧ p5) ∨ (False → ((True ∨ (p2 → p4)) ∧ False))) := by
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
theorem thm_5_vars_931740988980860483583210410498 : ((((((p3 ∨ p2) ∨ ((True ∨ p1) → p5)) ∧ True) ∧ ((p2 → p5) ∧ (True → (((((p5 → p4) ∨ p2) ∨ True) → False) ∧ (p5 ∨ p3))))) → p1) ∧ True) := by
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
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h3.left
      let h9 := h3.right
      -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h9, we can now drive its conclusion.
      let h11 := h9 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
      have h13 : (((p5 → p4) ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h12, we can now drive its conclusion.
      let h14 := h12 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h19 := h17 h18
      -- We need to get the left conjuct of h19 based on <expert-advice>.
      let h20 := h19.left
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : (((p5 → p4) ∨ p2) ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Conjunctions on the left can always be decomposed.
    let h24 := h3.left
    let h25 := h3.right
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- We need to get the left conjuct of h27 based on <expert-advice>.
    let h28 := h27.left
    -- We want to use the implication h28 based on <expert-advice>. So we show its premise.
    have h29 : (((p5 → p4) ∨ p2) ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h28, we can now drive its conclusion.
    let h30 := h28 h29
    -- False on the left can always be used.
    apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356170902625006870585004992311 : (p5 → ((p4 ∨ ((False ∧ ((True → (p2 ∧ p3)) ∧ ((p4 → ((p4 ∨ p1) ∧ False)) ∧ p4))) ∨ p2)) ∨ (((p4 → p3) → (True ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787572896820965783321754221065 : (((p4 ∨ (p1 ∨ (p1 → ((((p4 → p4) ∨ (p4 ∨ p4)) ∨ p3) → (p2 ∨ (((True → (p4 → p3)) ∨ False) → (p2 → (p1 ∨ True)))))))) ∨ p2) ∧ True) := by
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
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h14 =>
          -- False on the left can always be used.
          apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Implications on the right can always be decomposed.
        intro h17
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h1
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
  case inr h20 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h21
    -- Implications on the right can always be decomposed.
    intro h22
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h23 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338945892701280143940844303638 : (p1 → ((p5 ∨ p2) → ((((p1 ∧ (p2 ∧ (False ∧ (p5 → p5)))) ∨ (p1 ∧ (p1 → False))) ∨ p5) ∨ (((p2 ∨ False) → (True → p2)) ∨ True)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186304617806794904671911931652 : ((((((p3 → (p1 ∨ True)) → p4) → p2) ∧ (p4 ∨ p5)) → p4) → (((False ∧ ((p2 ∧ p1) ∨ False)) ∨ p3) → ((p1 ∨ p2) ∨ (p4 → True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192403316810441773517353394445 : (((((p4 → (p4 ∨ (p2 ∧ p2))) ∧ p1) ∨ True) ∨ p5) → ((p3 ∧ p3) → ((p2 ∧ p3) ∨ (((p2 ∧ (p1 → p2)) → (False ∧ p3)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172179008347636680171362672712 : (((p3 ∧ ((p5 ∨ ((p3 ∧ (True → False)) ∧ p5)) ∧ p5)) ∨ ((True ∨ p2) ∨ p1)) ∨ (((p3 ∧ (p5 ∧ (True ∨ (p5 → p2)))) ∨ p3) ∧ p4)) := by
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
theorem thm_5_vars_304777347294078309551440997531 : (p1 ∨ ((p4 ∨ ((p5 ∧ (False ∨ p2)) ∨ ((((p3 → ((p1 ∧ p3) → p3)) → p2) ∧ (p5 ∨ p5)) → (True ∨ (True → False))))) ∨ (p5 ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802949097688530498974002516138 : (((p3 → (((((p4 ∨ (p3 → (p4 ∨ ((p3 ∨ True) ∧ p5)))) → (False ∨ (p2 ∧ False))) ∧ (False ∨ ((p1 ∨ p4) → p4))) → p2) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606735474265785366925449226277 : ((((((((p5 ∧ p4) ∨ (True ∨ True)) → (((((p5 ∧ p1) ∨ (p3 ∨ (p1 → p5))) → p2) ∧ p1) → p4)) ∨ (p2 ∨ p3)) ∧ p3) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183493184934100991787384467357 : ((p3 ∨ (p2 ∨ (True ∨ (((p4 ∨ False) ∨ (p2 → p3)) ∨ False)))) ∧ ((((p3 ∧ p4) ∨ p1) ∨ (p5 → True)) ∨ (p3 → (p3 ∧ (p1 → p2))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140057738723765430595963329450 : ((((p3 → (((True → p5) ∧ p5) → p2)) ∧ ((p1 ∨ (p1 ∨ ((p2 ∧ p2) ∨ (p2 → True)))) ∧ True)) ∨ (p1 ∨ p4)) → ((p2 ∨ False) ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57047180713554265009059391202 : (((p3 → (p3 ∨ True)) ∧ (True → ((True ∨ p1) ∧ (((((False → (True → p2)) → p1) → (p4 ∨ ((p5 ∨ p2) ∨ p1))) ∨ p5) ∨ p2)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (False → (True → p2)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309616900545828764761138377351 : (p2 ∨ (((((p3 ∨ ((p2 ∧ ((p2 → p2) ∧ p4)) ∨ (p3 ∧ (p2 → False)))) ∨ (p5 ∧ p3)) → False) ∧ (p4 ∧ p4)) ∨ ((p4 ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_728506019205530782852587718921 : ((((p3 → (p2 ∧ p2)) ∨ (((p4 ∨ p5) ∨ (True ∧ p3)) ∨ ((p2 → ((p3 ∧ ((p5 ∧ True) → (p4 → p5))) ∧ p3)) ∨ (p5 → True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85339505828428853449010380759 : ((((True ∨ ((p5 → False) ∨ (p4 ∧ (True ∧ (p5 ∨ False))))) → p3) ∧ (False → (True ∧ (((False ∧ p1) ∨ p4) ∧ ((p2 ∧ p1) → p5))))) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ ((p5 → False) ∨ (p4 ∧ (True ∧ (p5 ∨ False))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302496336776302405617023689413 : (False ∨ (False ∨ ((((p1 → (p4 ∧ ((p4 → True) → ((p5 → (((True → p3) ∧ True) ∧ p5)) ∧ ((False → False) ∧ p3))))) ∨ False) → p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40526490626251052675004803208 : ((((False ∨ ((((((False ∨ p4) → p1) ∧ (True ∧ (p2 ∨ (False ∧ True)))) → p2) ∧ p2) ∧ (((False ∨ False) → False) → p4))) ∨ False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344514223692570438138742478233 : (p2 → (True → (p3 ∨ (((False ∨ ((True → False) ∧ ((p2 ∨ ((False → p4) ∧ (p1 ∨ (p2 ∧ (p5 → p4))))) ∧ (False → p3)))) ∧ p2) → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h14 := h8 h13
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h20 := h8 h19
        -- False on the left can always be used.
        apply False.elim h20
      case inr h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h8, we can now drive its conclusion.
        let h25 := h8 h24
        -- False on the left can always be used.
        apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182621033629956918224330938738 : ((((True → True) ∨ ((False ∨ True) → True)) ∨ (p3 ∧ (True → p3))) ∧ (((p2 ∧ (((p4 ∨ (True ∧ p2)) ∧ (False ∨ p1)) → p2)) → p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314702419104306752957877227270 : (p3 ∨ ((p5 → ((((p1 ∨ p5) ∧ (((False ∧ (False ∧ p3)) ∨ p3) → p3)) ∧ True) → p4)) → (False ∨ (((p1 ∧ (p3 ∨ p1)) ∨ True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_668079202331216518628373375655 : ((((True → (((p1 ∧ (((((p4 → p1) → True) → p4) ∨ ((p3 ∧ p2) ∨ True)) ∧ p5)) → (p2 → p2)) → False)) ∧ ((p2 → p3) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753995004550834855416488268885 : (((False ∧ (((p2 ∧ (p4 ∧ True)) ∧ True) ∧ (((p1 ∨ p3) ∨ (p1 ∨ (((p5 → (p1 → p4)) ∨ p4) → ((True ∧ p2) ∨ p1)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_5813419657619808624925376058 : ((((((p4 → True) → p4) → ((p4 ∨ (p3 ∧ (p3 ∨ (((p2 ∨ (p5 → p1)) → p3) ∧ p3)))) ∧ p4)) ∨ ((p2 ∨ p1) ∧ p4)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → True) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h5
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54425539542782251873762179039 : ((((((p2 ∧ p4) ∨ p2) ∧ (p3 ∨ p2)) ∨ True) ∨ ((p5 ∨ ((((p3 ∧ ((False → False) → False)) ∧ p3) ∨ p4) ∧ (p5 → p1))) → p1)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354888329136571712788418429813 : (p5 → ((p3 ∧ ((((True ∧ p5) → (((((p1 → True) ∧ p2) ∧ p5) ∨ (p1 → ((True → True) ∧ (p3 ∧ True)))) ∨ p3)) ∨ p5) → p4)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646058121491811367349298820280 : ((((True → (p2 ∧ ((False → (p4 ∧ (((p1 → p2) → True) → ((False ∧ p4) ∧ False)))) ∧ (p5 ∨ ((p2 → True) → (True ∧ p4)))))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60115668342241311632740080320 : (((p3 ∨ p4) → ((((p3 → True) ∨ (p2 ∧ (p5 ∨ (p5 ∧ ((p4 ∨ p1) ∧ ((p5 → ((p5 ∧ p2) ∧ p2)) ∧ p1)))))) → p1) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592947922278824572262664390109 : (((((p1 ∨ (((((p2 ∧ (p3 ∧ p3)) ∨ p1) ∨ True) ∨ (True → ((False → False) → p5))) ∧ (p4 ∧ p2))) ∧ ((False → False) ∧ True)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119553886521513261011589347456 : ((p5 → ((p3 ∨ ((False ∨ (True ∨ ((p5 → (p4 → p3)) → (True ∧ True)))) ∨ (p1 ∧ p1))) ∧ (False ∨ ((p2 ∨ p1) ∨ p3)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262100522276442239924670609025 : (True ∧ (((((((p1 ∧ (False ∨ ((p5 ∧ (p2 → (p3 ∨ p5))) ∨ (False ∨ p3)))) → (p1 ∧ p4)) ∨ (p2 → False)) ∧ False) ∨ p1) ∧ p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55699113117175789678195288671 : ((((p2 ∧ (p3 ∧ p1)) ∨ p4) ∧ (p2 → ((True ∧ ((p1 ∨ ((False ∨ True) → (((p4 ∧ False) ∧ p5) → p3))) → p4)) ∧ (True ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165366112699137307206526129824 : ((((False ∨ ((p4 → p4) → (p2 ∨ (p1 ∨ (p2 ∧ p3))))) ∧ p3) ∨ ((p1 ∨ True) ∨ p3)) ∨ ((p1 ∧ p3) ∧ (((False ∧ p4) → p4) → p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55631019072035772267339793965 : (((((False ∧ p5) ∧ True) ∧ p3) ∧ (p5 ∨ (((False ∧ ((p2 ∧ (p1 ∧ p1)) ∧ p2)) → ((True ∧ True) → p3)) ∧ (False ∧ (p3 ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_558970847994677315999510933672 : (((p4 ∨ (((p2 ∧ True) → ((p1 ∧ ((True ∧ ((p1 ∨ p3) ∧ ((False → (p2 ∨ (p1 → p3))) ∨ p3))) ∧ p2)) ∨ (p1 ∨ p3))) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339711734725402334555142670978 : (p1 → (p3 ∨ (True → (((p5 ∧ p2) ∨ p3) ∨ (p1 ∧ (((p4 ∨ p3) ∧ ((False → p1) ∨ p4)) ∨ ((p1 → ((False ∨ p4) ∧ False)) → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172031700618218802123417988482 : (((p1 ∧ (p1 → ((p5 ∨ (p2 ∧ (p2 ∧ False))) ∧ (p5 → False)))) ∨ (p4 → p1)) ∨ ((False ∨ ((True ∨ ((False ∧ p5) → p5)) → p1)) → p1)) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (True ∨ ((False ∧ p5) → p5)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698954783475485824876923696593 : ((((p5 ∧ (((p1 → True) ∧ ((p5 ∨ (p3 → False)) → p2)) ∨ p1)) ∨ ((((p3 ∧ p4) → p5) ∧ (((p3 ∧ p4) ∨ False) ∨ False)) ∨ True)) ∨ p4) ∧ True) := by
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



