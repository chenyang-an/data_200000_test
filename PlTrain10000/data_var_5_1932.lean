variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330433176668129864230243908368 : (True → (p3 ∨ ((False ∧ ((p3 → ((((True ∧ p2) → p3) ∧ False) ∨ True)) ∧ ((True → (False ∧ False)) ∨ (p4 ∧ True)))) ∨ (p3 → (p3 ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263067965524178985561256709566 : (True ∧ ((((True ∨ (p3 ∧ (True ∨ ((p3 ∧ ((p5 ∨ p4) → (p3 ∨ ((p2 → p1) ∨ (p3 ∨ p3))))) ∧ p4)))) → p5) ∧ p3) ∨ (True ∨ p1))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317045268431526413581019609553 : (p3 ∨ (p4 → ((((p4 ∨ (p2 → True)) ∧ (False ∨ (p1 ∧ (p2 ∧ ((((p1 ∨ (False → p3)) ∨ p1) → p2) ∧ p3))))) ∧ p1) ∨ (p4 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163550034375525787388749789900 : (((p4 ∨ (p2 ∧ p5)) → ((p5 ∧ ((((p2 ∧ p2) → True) → (p2 ∧ False)) ∧ p3)) ∨ True)) ∧ (False → (False ∧ ((p3 ∧ (False ∨ False)) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205295885878096672813415979912 : (((p4 ∧ (p1 ∨ p1)) ∨ (p3 ∨ False)) ∨ (((((((p1 → (True ∧ p3)) → p2) ∧ ((p3 → p1) ∧ (p1 ∧ p5))) ∨ p1) ∧ False) → False) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157510602449054335678997419634 : (((p3 ∧ (p1 ∧ ((p5 ∧ False) ∨ ((p5 → (((p4 ∨ p1) → p4) ∧ True)) → p4)))) ∨ (p1 ∨ p3)) ∨ ((((p5 → True) ∨ False) ∨ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346005938743193897708585473535 : (p3 → ((((p1 ∨ p3) ∨ p2) → (p2 ∧ (((p1 ∧ p5) ∨ ((p3 → p4) ∧ (((p1 → ((p4 ∧ p2) ∨ p3)) ∨ True) → p2))) ∧ p1))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ p3) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256046306414342474707199246083 : ((True ∨ p4) → ((((p1 ∧ False) ∨ (((False ∧ p2) → (p3 ∨ p2)) → (p5 → ((True ∨ True) ∧ (p3 ∨ p2))))) ∧ True) ∨ (False → (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718980470508542096388990790712 : (((((p4 ∨ p5) → (p5 ∨ p1)) ∨ ((((p4 ∨ (p1 → p4)) ∧ (((p3 → p1) ∨ p4) ∧ ((False → (False ∨ p3)) → False))) → p5) ∨ p5)) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (False → (False ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- False on the left can always be used.
        apply False.elim h9
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h8
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (False → (False ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h14 := h6 h12
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h3.left
    let h17 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h19 : (False → (False ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h21 := h17 h19
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h23 : (False → (False ∨ p3)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h25 := h17 h23
      -- False on the left can always be used.
      apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140073562544828503420123348251 : ((((p2 ∨ p5) ∧ ((p3 → True) ∨ (p1 ∨ (p4 ∧ ((p3 → (p3 → p1)) ∧ (p3 ∧ (p2 ∧ p2))))))) ∨ (False ∧ p3)) → (False ∨ (True ∨ False))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- Conjunctions on the left can always be decomposed.
          let h27 := h26.left
          let h28 := h26.right
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h31 =>
    -- Conjunctions on the left can always be decomposed.
    let h32 := h31.left
    let h33 := h31.right
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172394718213071359382931539359 : ((((p2 → p2) ∨ ((False ∧ p5) ∧ False)) → ((p5 ∨ (p5 → p2)) ∨ (True → False))) ∨ ((p3 ∨ p5) → ((p1 ∨ (True ∧ p1)) → (False → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85824872619423809928444359823 : ((((p4 → p1) ∨ ((p4 ∧ p3) ∨ (False ∨ (p1 → (p1 ∨ p5))))) → ((p3 ∧ False) ∧ ((((p3 ∨ True) ∨ p1) → (False → p1)) → False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → p1) ∨ ((p4 ∧ p3) ∨ (False ∨ (p1 → (p1 ∨ p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351525613966657616334234169474 : (p4 → (((p1 → ((p5 → (((p1 ∧ p2) → p4) ∨ (p3 ∨ (p4 ∨ p1)))) ∨ (True → p1))) → p3) ∨ ((True ∨ (p1 → p1)) → (p5 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42665924674020884072200645204 : (((p4 ∨ (((True → (p5 ∨ p1)) → p2) ∨ (p5 ∨ (((((True ∨ (p1 ∧ p4)) ∧ (True ∨ False)) ∨ p2) → p4) ∨ (p2 → p5))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182013924370346336000339604629 : ((((((p3 → (p5 ∨ p5)) → False) → p5) → (p2 → False)) ∨ True) ∧ (p2 → ((((True ∧ False) → True) ∨ True) ∨ ((p2 ∨ (True → True)) → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977491233226060996592414536138 : (((True ∧ ((p2 ∨ (p1 ∧ (p5 ∧ (True ∨ p2)))) ∧ (((True ∨ False) → (False ∧ (p5 ∨ p4))) ∧ ((((p3 → p5) → p4) ∨ p5) ∧ p2)))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h9
    case inl h11 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h12 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h13 := h7 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h16 : (True ∨ False) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h16
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h5.left
      let h26 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h30 : (True ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h31 := h25 h30
        -- We need to get the left conjuct of h31 based on <expert-advice>.
        let h32 := h31.left
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h34 : (True ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h35 := h25 h34
        -- We need to get the left conjuct of h35 based on <expert-advice>.
        let h36 := h35.left
        -- False on the left can always be used.
        apply False.elim h36
    case inr h37 =>
      -- Conjunctions on the left can always be decomposed.
      let h38 := h5.left
      let h39 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h40 := h39.left
      let h41 := h39.right
      -- Disjunctions on the left can always be decomposed.
      cases h40
      case inl h42 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h43 : (True ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h44 := h38 h43
        -- We need to get the left conjuct of h44 based on <expert-advice>.
        let h45 := h44.left
        -- False on the left can always be used.
        apply False.elim h45
      case inr h46 =>
        -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
        have h47 : (True ∨ False) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h38, we can now drive its conclusion.
        let h48 := h38 h47
        -- We need to get the left conjuct of h48 based on <expert-advice>.
        let h49 := h48.left
        -- False on the left can always be used.
        apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38286515764884522225928513949 : (((((p4 ∧ False) ∨ ((p2 → (False ∧ (False ∨ False))) ∧ (p2 ∨ (((p2 ∨ p5) → p1) ∨ p4)))) ∨ ((p4 → (True ∨ p5)) ∨ True)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247560365962722078478734064995 : ((False ∨ p4) ∨ ((p1 ∧ (p4 → False)) → (p1 ∧ (p4 ∨ ((((((p4 ∨ p1) → p3) → p5) ∧ p5) ∨ p1) ∧ (p2 → ((True → p4) → p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178261271241066286342272773703 : (((((((p4 ∨ True) ∨ p2) → p2) ∧ p5) ∨ (p2 ∧ p3)) ∧ (p2 ∨ p5)) ∨ (((p2 ∧ (True ∨ p1)) → (p1 ∨ (True → p1))) → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148889275209247311164464201474 : ((((p3 ∨ p2) ∨ (p4 ∧ p5)) ∨ ((((p1 ∨ p4) ∨ p4) ∨ ((p4 ∨ False) ∨ ((p5 → p4) ∧ p5))) ∧ True)) ∨ (p4 → ((False → p2) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227665188227241433191203289975 : ((False ∧ (p2 → False)) ∨ (((p4 → (((p4 ∧ p2) → ((p5 ∧ (p5 ∧ (p3 → p4))) ∨ p3)) ∧ p5)) → (False ∧ (True ∨ p2))) ∨ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174046233461430943862981506572 : (((True → (p3 ∨ (p3 ∨ (((p2 ∧ p2) → ((True ∨ p3) ∨ False)) → p5)))) → False) → ((False ∨ p5) → (((p1 ∨ True) → (p1 ∨ p1)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (True → (p3 ∨ (p3 ∨ (((p2 ∧ p2) → ((True ∨ p3) ∨ False)) → p5)))) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h13 := h1 h10
      -- False on the left can always be used.
      apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300564995687189348023867721203 : (False ∨ ((False ∧ (((True → (((False ∧ p1) → True) → p5)) ∨ True) ∧ (((p4 ∧ True) → (False → p5)) ∧ p1))) ∨ ((p4 ∨ (p1 ∧ p3)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149001305924140236889976152994 : (((p4 → (False → p4)) ∧ ((((((p4 ∨ (((p5 → p2) ∨ p4) ∨ True)) ∨ p2) ∨ True) ∨ p1) ∧ p5) ∨ p1)) ∨ (False ∨ (p4 → (p3 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207236456425306309083066219858 : (((((True ∨ p1) → True) ∨ p4) ∨ p5) → ((((p1 → (p3 ∧ ((p2 → True) ∨ p5))) → p5) → (p5 ∧ p2)) ∨ (p3 ∨ ((True → True) ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165765697135962167749591282756 : ((((p1 → (p4 ∧ p5)) ∧ p5) → (False ∧ ((((True ∨ p4) → p4) ∨ True) → (p2 ∨ p5)))) ∨ (((p3 ∧ (p2 → (False ∨ p1))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245911629763998506518664997177 : ((p3 ∧ p5) ∨ (((((p5 → p3) ∧ p4) ∨ False) ∨ (p1 ∨ ((p3 ∧ p2) ∨ p1))) ∨ (((True ∨ ((False ∧ False) ∧ p3)) ∨ p4) ∨ (False → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_247938981337938187419288634897 : ((p1 ∨ p3) ∨ (p3 ∨ (((False ∧ ((((p4 ∨ True) ∧ p1) ∨ True) → False)) ∨ (True ∨ ((False → (True ∨ p3)) ∧ p3))) ∧ ((p4 ∧ p1) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729472372894004258847950886495 : (((((False ∨ True) ∨ p2) → (p2 ∨ (p2 ∧ ((p1 → (p4 ∨ p3)) ∧ (p3 → ((p3 → (((p4 ∧ p1) ∧ False) ∧ (p3 ∨ p1))) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44366109097253032984766892538 : ((((((p2 ∨ False) → ((False ∨ p1) → p4)) ∨ (p2 → ((p2 → p2) ∨ p2))) ∧ ((p5 ∧ ((p3 → p3) ∨ p1)) → (p5 → True))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637798835818751560731677715193 : (((((p4 → (p2 ∧ ((p5 → ((p1 → p4) ∨ p4)) ∧ p1))) → (((False ∨ p2) ∨ ((((p3 ∧ p1) ∧ p2) ∧ p4) → p5)) ∨ p1)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2689456582255578864668491169 : (((((p2 → p5) → p3) → True) → False) → (((((((p5 → (False ∨ p3)) ∨ True) ∧ True) → p5) ∧ ((p4 ∧ p3) → p3)) → p3) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 → p5) → p3) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178854298306050789906192571253 : (((p4 ∧ (p4 ∨ p3)) → (p2 → ((False ∧ (p3 → (False ∨ p5))) ∧ p4))) ∨ ((p5 ∨ ((((p4 ∨ (p5 ∨ False)) ∧ p4) ∨ p5) ∨ True)) ∨ p5)) := by
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
theorem thm_5_vars_171739397100037303132529300206 : (((((False ∨ (((p5 → p5) ∧ p5) ∨ ((False ∨ p4) ∨ p2))) → True) ∨ p3) → p4) ∨ (p5 → ((p1 ∧ (((p4 ∧ False) → p5) ∨ p2)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139802454243025832638307371164 : (((p4 ∨ ((((p2 ∧ (((False → p3) ∨ p1) ∧ p1)) → p3) ∧ ((p1 ∨ (p1 ∧ (p1 → p4))) ∧ p3)) ∧ p4)) → p4) → (p4 ∨ (p3 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166590886858114121718609022604 : ((True → ((p3 → p4) → (((p1 ∧ p1) → (((p2 ∧ p4) ∧ (p1 ∧ False)) ∨ p1)) ∧ p3))) ∨ (((True → p2) → p2) ∨ (True → (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_177970231020382465813195186101 : ((((p3 → False) → ((False ∧ (((True → p2) ∨ p4) ∧ p4)) ∨ p2)) ∨ p5) ∨ (True → (True ∨ (True ∧ ((True → p3) ∧ (p5 → (p5 ∨ p3))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47266039064022820784517589394 : (((((p3 ∨ (p1 → p4)) ∧ p5) ∧ (((p4 ∧ p1) ∧ (p1 ∧ ((p5 ∧ (p5 ∨ (p3 ∧ p2))) ∧ (p3 ∧ p1)))) ∧ p1)) ∨ (True ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634702706496321376432819855891 : (((((((p2 ∧ (p4 → (p4 → p2))) → (((p3 ∧ False) ∧ ((p2 → p2) ∧ (p3 → True))) ∧ p4)) ∨ p1) ∨ ((True ∧ False) ∧ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625285919815574239018197709637 : ((((True → (p4 → ((p4 ∧ (((False ∧ (False ∧ False)) → (False ∧ p4)) ∨ ((p4 ∧ True) ∨ (((True ∧ False) ∨ p5) ∧ p2)))) → p5))) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_464049184587077930825904499041 : (((((((p2 → (True → p2)) ∧ (False ∨ (p1 ∨ (True ∧ (True ∧ p4))))) ∨ p3) ∨ p3) → (((p1 ∧ p1) ∨ p4) ∨ ((p1 ∧ p5) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- Conjunctions on the left can always be decomposed.
          let h12 := h11.left
          let h13 := h11.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
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
theorem thm_5_vars_112749764580109380279630804884 : (((((p4 ∨ (p5 ∨ False)) ∨ (p2 ∨ (False → (p1 ∧ (True ∨ True))))) → ((p4 ∧ (((p1 ∧ p4) ∧ p3) ∧ p5)) → p1)) → p4) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249006067355082650407152854051 : ((p4 ∨ False) ∨ ((((p2 ∧ False) ∨ ((p1 ∨ p1) ∨ p2)) ∨ (((p1 ∧ (p2 ∧ p3)) → p2) ∧ p3)) ∨ (p4 ∨ ((False ∧ (p5 ∧ False)) → p2)))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40242058521878461552635115393 : ((((p4 ∧ (p5 → (((((True ∧ (p1 ∨ p5)) → False) ∨ ((False ∧ (p2 ∧ ((p5 ∧ p4) ∨ False))) ∧ False)) ∨ True) ∨ True))) ∧ p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107770732942555520760369655622 : (((False ∧ p3) ∨ ((False ∧ ((p3 ∨ False) ∨ (p1 ∧ (False ∨ (p2 → ((p3 → ((p1 → (False → p1)) → False)) → p3)))))) ∨ True)) ∧ (False → False)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307967518044914631653887901043 : (p2 ∨ ((((p1 → p4) ∧ (((((True → p1) → p5) → (p1 → (p3 ∨ (p2 ∧ p5)))) ∨ True) ∧ (p1 → ((True ∨ True) → False)))) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_314716735435919728220047043193 : (p3 ∨ (((p4 ∨ (p1 → ((p5 ∧ False) → p2))) ∧ (p5 ∨ ((p3 ∧ p3) → True))) ∧ ((p3 ∧ (p1 ∨ (p5 → (p4 ∧ (p4 → p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139669738091672717866073212573 : (((((p1 ∧ False) ∨ p4) ∧ ((p4 ∧ (((((p2 ∨ ((p1 → False) ∨ p3)) ∧ p4) ∨ p4) ∨ p3) ∨ p3)) ∧ p4)) → p3) → ((True → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50046507664302214731435544747 : ((((True ∨ (p1 ∨ True)) → ((((p4 → p1) → ((p2 ∨ (p5 ∧ False)) → p3)) ∧ (False ∧ p2)) ∨ p2)) ∧ (((p2 ∧ p1) ∨ p3) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114860643050104318724552202353 : ((((p2 ∨ (p5 ∧ ((False ∨ False) ∧ (p1 ∨ (p2 ∨ False))))) ∨ (True ∨ p3)) ∨ (((p1 ∨ p4) ∧ p2) ∧ ((p1 → p3) ∨ p1))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118213247218921727762756103185 : ((p1 ∨ (((p2 ∨ p1) ∧ ((True → ((((p1 → p1) ∧ (p4 ∨ p2)) → p3) → p1)) ∧ (p1 → ((True ∧ p2) → p5)))) ∧ p2)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145491462453916787877325919738 : ((((p4 ∨ p2) ∨ True) ∧ ((p4 → (p4 → (p3 ∨ (p5 ∨ (p4 ∨ p2))))) ∨ ((p4 ∨ (p3 → True)) ∧ p1))) ∧ (((False ∨ p2) ∧ p4) ∨ True)) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47857693897766359037639617395 : ((((p5 → (p3 ∨ ((p2 ∨ ((False ∧ ((p3 → p5) → (False ∧ p3))) ∧ (p5 ∨ (True → p5)))) → (p1 → p3)))) → False) → (p5 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52745622981695746757110387071 : ((((p1 ∧ (((p3 ∧ ((p1 → False) ∧ (p4 ∨ p1))) ∧ p4) → p1)) ∨ p3) → ((((p2 ∨ p2) ∨ p4) ∨ p1) ∧ (p5 ∧ (p1 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617542663083751838697762096781 : ((((((p1 → p3) ∨ (p5 ∨ (False → p4))) ∧ (False ∧ (((p2 → ((p2 ∨ (p1 ∨ p1)) → (p4 → (True → True)))) → p2) ∧ p2))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_186543419141081497064473249353 : (((((p3 → True) ∨ p2) ∧ (p5 ∨ (p5 ∧ p4))) ∨ (p5 ∨ p3)) → ((p4 → ((True ∧ ((True ∧ False) ∨ p2)) → (p3 ∨ (p2 ∧ p4)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h9
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h18
          -- One of the premise coincides with the conclusion.
          exact h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h9
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h25 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319224873508356799555575091109 : (p4 ∨ ((True → (((p5 → (p1 → p2)) ∧ ((p5 → (True ∧ ((p4 → p2) ∧ False))) ∧ p2)) ∧ p2)) → ((p5 → (p5 ∧ (p4 ∧ p1))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- False on the left can always be used.
  apply False.elim h11
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h12 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h12
  -- We need to get the left conjuct of h13 based on <expert-advice>.
  let h14 := h13.left
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- We need to get the left conjuct of h15 based on <expert-advice>.
  let h16 := h15.left
  -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
  have h17 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h16, we can now drive its conclusion.
  let h18 := h16 h17
  -- We need to get the right conjuct of h18 based on <expert-advice>.
  let h19 := h18.right
  -- We need to get the right conjuct of h19 based on <expert-advice>.
  let h20 := h19.right
  -- False on the left can always be used.
  apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65651732156809421165890656813 : ((p4 ∨ ((p4 ∧ ((((p2 ∨ (((p5 → p5) ∨ p5) → True)) ∧ p3) ∨ (p2 ∧ ((p4 ∨ ((p2 → p5) → p3)) ∨ True))) → p1)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_927447132832131530939740505561 : ((((((p1 ∧ ((p4 → True) ∨ p5)) ∨ (p1 → p1)) ∨ p2) ∧ ((p4 ∨ (((p5 ∧ False) → (p4 ∨ (False → p2))) → (True ∧ True))) → p4)) → p4) ∧ True) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : (p4 ∨ (((p5 ∧ False) → (p4 ∨ (False → p2))) → (True ∧ True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h9
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p4 ∨ (((p5 ∧ False) → (p4 ∨ (False → p2))) → (True ∧ True))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (p4 ∨ (((p5 ∧ False) → (p4 ∨ (False → p2))) → (True ∧ True))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h17
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h21 : (p4 ∨ (((p5 ∧ False) → (p4 ∨ (False → p2))) → (True ∧ True))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h23 := h3 h21
    -- One of the premise coincides with the conclusion.
    exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231508472969918379775783371315 : (((p4 → True) ∨ p3) → ((p2 ∧ p2) ∨ (((p4 ∨ p3) → ((p4 → p4) ∧ p4)) → ((p4 ∨ p5) → ((True ∧ p3) → ((p5 ∧ p5) → p4)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h13 : (p4 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
  case inr h16 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Implications on the right can always be decomposed.
    intro h19
    -- Implications on the right can always be decomposed.
    intro h20
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- Conjunctions on the left can always be decomposed.
    let h23 := h19.left
    let h24 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h25 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h26 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h27 : (p4 ∨ p3) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h28 := h17 h27
      -- We need to get the right conjuct of h28 based on <expert-advice>.
      let h29 := h28.right
      -- One of the premise coincides with the conclusion.
      exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232208873191114296312333444628 : (((False → p5) → False) → ((True → ((p1 ∧ p4) ∧ False)) ∧ ((True → p1) ∧ ((p5 ∧ (p2 ∨ p3)) ∧ ((p4 → p2) ∨ ((False ∧ p4) → p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- False on the left can always be used.
    apply False.elim h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h13
  -- False on the left can always be used.
  apply False.elim h15
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- False on the left can always be used.
    apply False.elim h17
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h18 := h1 h16
  -- False on the left can always be used.
  apply False.elim h18
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h19 : (False → p5) := by
    -- Implications on the right can always be decomposed.
    intro h20
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h21 := h1 h19
  -- False on the left can always be used.
  apply False.elim h21
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h22
  -- Conjunctions on the left can always be decomposed.
  let h23 := h22.left
  let h24 := h22.right
  -- False on the left can always be used.
  apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187246126199288259229911361096 : ((True ∧ (((p3 → (p3 ∧ True)) ∧ p1) ∧ (True ∨ (p4 → p2)))) → (p2 → (p2 ∧ (p2 ∧ (p2 → ((True → ((p3 → p3) ∨ True)) ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Disjunctions on the left can always be decomposed.
  cases h14
  case inl h17 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h19
  -- Conjunctions on the left can always be decomposed.
  let h20 := h1.left
  let h21 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h22 := h21.left
  let h23 := h21.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h22.left
  let h25 := h22.right
  -- Disjunctions on the left can always be decomposed.
  cases h23
  case inl h26 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h25
  case inr h27 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_36257153690515559386501176085 : ((p4 → (((False ∨ (p5 → ((p3 ∨ p3) → True))) → (p2 ∨ (((p3 ∨ p4) → p3) ∨ (((p5 ∨ p4) ∧ (p1 → p5)) → True)))) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204759838459562864420172079022 : (((((p4 ∨ True) ∧ p3) ∧ p5) → False) ∨ (((p5 ∨ ((((False ∧ (p4 → p5)) → False) ∨ p3) ∨ p2)) ∧ p4) → (p2 → (p5 → (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149878074751454352094236322771 : ((p2 ∨ ((False → (p4 ∧ (p2 ∨ ((p2 ∧ (p1 ∧ True)) → ((True ∨ False) → p5))))) → (p5 → (p3 ∨ p1)))) ∨ ((p4 → p4) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185339914179970954559341881114 : ((p4 ∧ (((p5 ∨ ((p1 → True) → False)) ∧ (False ∨ p5)) ∨ p1)) ∨ (False → (p2 → (p4 ∧ ((p3 ∨ ((False ∨ p2) ∨ (p4 ∨ p4))) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247738247687695711462534471279 : ((p1 ∨ False) ∨ ((False ∨ (((p1 → False) ∧ p1) ∧ p4)) → (((p4 ∧ (((p4 → (p2 ∧ p3)) ∨ False) → p5)) → ((False ∨ p1) → False)) ∨ False))) := by
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
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h8 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149889794798144319336114265422 : ((p2 ∨ ((p4 ∧ p4) ∨ ((p5 ∨ (p4 ∨ (p3 → (p3 ∧ ((p1 → p4) → (p5 → False)))))) ∨ (p4 ∧ p1)))) ∨ (((p2 → p4) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135461008739434652864132239280 : ((((False ∨ (True ∧ ((p3 → (p2 → p2)) ∧ ((p1 ∨ ((p1 ∧ p4) → p3)) ∧ p1)))) → False) → ((p4 ∨ p4) ∧ p5)) ∨ (True ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260916038104147595392214733102 : ((p4 → False) → ((p2 ∧ (p1 → (True ∨ (p3 → p3)))) ∨ ((p2 → p3) ∨ (p4 → (True → (p5 ∨ ((False → ((p1 ∧ p5) → p4)) → p3))))))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315135151545738078708626461253 : (p3 ∨ ((p1 ∨ (((p1 ∧ p1) ∧ p2) ∨ p2)) ∨ (((p4 ∧ (((False → p4) ∧ (p3 → (p1 ∨ p1))) ∧ p4)) → (p5 ∨ (True ∨ p2))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614910392393379941118849281728 : ((((((p2 ∧ (p5 → (((p3 ∧ (p1 ∧ p4)) → False) ∧ (p1 → ((p3 ∧ p3) ∧ p3))))) ∨ p3) → ((False ∨ (p3 → p2)) ∧ p4)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_729670613577420313838226243077 : (((((False → p4) ∨ p2) → ((p5 → (p4 ∨ (p2 ∨ False))) → (((p1 ∧ p3) ∨ (p2 ∧ p2)) ∨ (True ∧ (True ∨ ((p1 ∧ False) ∨ True)))))) ∨ False) ∧ True) := by
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
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41082193233054654160546557000 : (((((((p4 ∧ p5) ∨ p1) ∨ (p4 → ((True ∨ ((p5 → (False ∧ True)) → True)) ∧ (False → False)))) ∧ p3) ∧ ((p5 ∧ p4) ∨ p5)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342744788155573031572127371924 : (p2 → (((p3 → (p4 → (p2 ∧ (p3 ∨ p2)))) ∧ p4) ∨ ((False ∧ (p4 ∧ p5)) ∨ (((False → (True ∧ (p3 ∧ p5))) → p1) ∨ (p1 ∨ True))))) := by
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
theorem thm_5_vars_52352370407180096126230472066 : ((((((((p3 ∧ (p1 → p3)) ∧ False) → p5) ∧ p2) ∧ True) ∧ (False → p4)) ∧ ((((p3 → True) → p4) ∨ (p5 → (p4 ∧ p2))) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648548110596246906892578959262 : ((((((p2 ∧ (((p4 ∧ (p1 → (False ∨ p5))) ∨ (False ∨ p3)) ∧ (p3 → p1))) ∨ (p3 → (p4 ∨ (p3 ∧ p1)))) ∨ p5) ∧ (p5 ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717841416803668492192383700188 : (((((p2 ∧ (p3 ∧ p3)) ∧ False) ∨ ((False → (((p5 ∧ p4) ∨ ((False → (p4 → (p4 → p5))) ∧ (p5 → p4))) ∨ (p1 → p1))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137460548366606738465474312168 : ((p4 ∧ (False ∧ (p5 ∧ ((False ∧ ((p3 → p1) ∧ (p1 ∨ (p2 ∧ (p3 ∨ (False ∨ (p4 ∨ (True ∨ p4)))))))) ∧ True)))) ∨ ((p2 → p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231957870250395184467232597454 : (((p1 ∨ p2) → p3) → (((p1 ∧ (((((p2 ∧ True) ∧ (((True ∧ p5) ∨ True) ∨ p1)) → p3) ∧ (True → p1)) ∧ (False → p3))) ∨ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58145849630297069530861411839 : (((p2 ∧ p3) ∧ (p5 ∨ (False ∧ (((((((p3 → True) ∧ ((p4 ∧ p1) → p1)) ∨ p3) → (p3 → False)) → (p1 ∨ p1)) → p3) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313340343740729751292386123024 : (p3 ∨ ((True → (p2 ∧ (True → ((p3 ∧ (p1 ∧ (p2 → ((False → p2) ∨ (((p4 ∧ True) → False) ∨ ((p1 ∧ p4) → True)))))) ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245334042995734277047546712008 : ((p2 ∧ p2) ∨ (p4 → (((p4 ∧ ((p4 → ((True ∧ p1) ∨ (p3 ∨ p2))) ∧ p3)) ∨ ((p3 ∨ p1) → (p2 ∧ p3))) ∨ ((False ∧ p2) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307380998303466794546259181811 : (p1 ∨ (p4 ∨ ((p5 ∨ ((False ∧ (((((p5 → p5) → True) ∨ p4) ∧ ((p3 → p5) ∨ p3)) ∧ True)) ∧ False)) ∨ (((p3 ∧ p5) ∨ True) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41099320023372351126795097719 : ((((((True ∧ False) → ((p3 ∧ True) ∨ ((p2 → p1) → (p2 ∨ p3)))) → ((p3 ∧ (True → p5)) ∧ p1)) ∧ ((p2 ∨ p3) ∧ False)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114609921505316658258086083485 : (((p4 ∨ (True → (False ∨ (p1 → ((((False ∨ p1) ∧ (True ∨ False)) ∧ p1) ∨ p3))))) ∧ ((p2 → (p1 → (p1 → p1))) → False)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745591922049593339759166332022 : ((((True ∨ p2) → (((((True ∨ (p2 → p1)) ∧ p2) → (True ∨ (True ∧ ((p4 → (True → p4)) ∧ (p3 ∧ (p1 → p1)))))) ∨ False) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185326719761245320320846509963 : ((p3 ∧ (False ∧ ((p5 → (False ∨ p2)) → (True ∧ (p4 ∨ p4))))) ∨ (False → ((p5 ∧ (p2 ∨ p3)) ∨ (((p2 ∧ (p3 ∨ False)) ∧ p5) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340131625334393019754890971320 : (p1 → (p3 → (False ∨ (((p2 → (p5 → (p1 ∨ (False ∧ (False ∧ (p1 ∧ ((p3 ∧ (p1 → p2)) → (p2 → (p2 ∨ p5))))))))) → False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308530042795199338095756870635 : (p2 ∨ (((p4 ∧ ((p1 ∨ (((p1 ∨ False) ∧ p5) ∨ (p5 ∧ (p1 ∨ True)))) ∨ p3)) → (p2 ∨ (p5 ∧ ((False ∨ True) ∨ (True ∨ p5))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241640123859057850845740064327 : ((False → p5) ∧ (((p1 ∨ True) ∧ ((p1 ∨ p2) ∨ (p4 ∧ (((p4 ∧ p5) ∨ (((p2 ∧ ((p3 ∨ p4) ∨ p2)) ∨ False) ∨ p5)) ∧ p2)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206156901750994619146639975085 : ((p5 ∧ (((p5 ∨ p2) → False) ∨ p2)) ∨ (p1 → (p3 ∨ (((True ∧ p2) ∨ p4) ∨ ((p5 ∧ ((True → (p2 ∨ p4)) ∧ (True ∨ p5))) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_179458371314540368912932089992 : ((p5 ∨ ((p1 → p3) → (((p3 → (p2 ∨ True)) ∧ True) → (p4 ∧ p1)))) ∨ (p1 → (((p2 → (p5 ∨ (True ∨ (p1 → False)))) ∧ p3) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247600640285020244087828347571 : ((False ∨ p5) ∨ ((True → (((p4 → (((p2 ∧ (False → p1)) → (False ∨ (p2 ∧ p3))) ∧ False)) → (False ∨ (True → p2))) ∨ True)) ∧ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68712046394406781819347068041 : ((p4 → ((((p4 ∨ p1) ∨ p4) → (((((False ∧ p5) → (((True ∧ True) ∨ p1) → p1)) ∨ False) ∨ False) ∧ False)) ∧ ((False ∧ p4) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179547763293382481466727048357 : ((p1 → (p2 ∧ ((False ∧ (((p3 ∧ p4) → p4) ∧ False)) ∧ (p4 ∧ True)))) ∨ ((p3 ∧ (False ∧ False)) ∨ ((p1 ∧ p4) → (p1 → (p3 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159316733901650056132121157005 : ((p5 → (((p1 ∨ (((((True → p2) ∨ True) ∨ False) ∨ p3) ∨ p2)) → True) → ((p1 → True) ∧ False))) ∨ ((((True → p3) ∧ False) → False) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152183163827272867734709296983 : (((((p3 → (p2 → p5)) ∨ p2) → (True → p1)) → (p1 → (((p2 → p2) ∧ (p4 ∨ p3)) → (False → p1)))) → ((p5 ∧ True) → (p1 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42729181209230443599927251537 : (((True → ((p4 → ((p1 ∨ True) → (((p3 ∧ p2) ∧ (p2 → (False ∨ p5))) ∧ (p2 → (False ∧ ((p2 → p1) → True)))))) ∨ p3)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147033412272688746563018527190 : (((((p2 ∧ (((True ∨ (p2 → False)) ∨ (p3 ∧ True)) ∨ (p5 → p3))) → True) → ((p2 ∨ p3) ∧ True)) ∧ p1) ∨ (p4 → (p1 ∨ (True ∨ True)))) := by
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



