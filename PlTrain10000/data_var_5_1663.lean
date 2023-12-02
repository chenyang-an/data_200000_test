variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160775418176421371529646021392 : (((True ∨ (((p5 ∧ False) → False) ∧ p2)) ∧ (((p3 ∧ (p3 ∨ True)) ∨ True) ∨ (p2 ∨ (p5 → p1)))) → (p1 → ((p5 ∨ (False → p1)) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        case inr h12 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h15
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h21.left
    let h23 := h21.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h25.left
        let h27 := h25.right
        -- Disjunctions on the left can always be decomposed.
        cases h27
        case inl h28 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- False on the left can always be used.
          apply False.elim h29
        case inr h30 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
      case inr h32 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h33
        -- False on the left can always be used.
        apply False.elim h33
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h36
        -- False on the left can always be used.
        apply False.elim h36
      case inr h37 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h38
        -- False on the left can always be used.
        apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657644276738840454107931692988 : (((((p1 ∨ p2) → ((p4 ∧ ((p1 ∧ ((p1 ∨ (p5 ∨ False)) ∧ ((p1 ∧ False) ∨ True))) ∧ (True ∨ p4))) ∨ (True ∨ p2))) ∨ (True ∧ True)) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149115505988747102807646695076 : (((True ∧ p5) ∧ (True → ((p2 → (False ∨ (p3 ∨ p5))) → (((True ∧ (p3 ∧ (p2 ∨ p5))) ∨ p3) → p5)))) ∨ ((p2 → True) ∨ (p1 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136358490277601405839603484639 : (((((p1 ∧ False) → p1) ∧ p1) ∨ ((p5 ∨ True) ∧ ((p1 → (((p3 ∧ ((p5 ∨ p1) → p2)) ∧ True) → p3)) → p3))) ∨ (True ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598774718139042371365160050483 : (((((p1 ∧ p2) ∧ (True → (p1 ∨ ((p4 ∨ (False → (((True ∨ False) → p2) ∧ (p1 → ((p5 → p3) → p3))))) ∧ (p4 → True))))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201078233260603310886697169561 : ((p5 ∨ ((True ∨ p1) → ((False ∨ p5) ∨ True))) → (((p4 → p2) ∨ p2) → (((p3 ∨ p1) ∧ (True → p5)) ∨ (p5 → ((p4 ∨ False) → p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h8 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h7
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h9 := h3 h8
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h15 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h16 := h3 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h20
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h23 =>
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Disjunctions on the left can always be decomposed.
      cases h26
      case inl h27 =>
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h28 =>
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653857066197718798931694385144 : ((((((((p4 → False) ∧ (p2 ∧ p2)) ∧ p5) → (False ∧ ((p4 ∨ False) ∨ (False ∧ (p5 → (p3 → (p3 ∧ p1))))))) ∧ p4) ∨ (p3 ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_256967123279975730223327235111 : ((p1 ∨ p5) → ((True ∧ ((p3 ∨ (p2 ∨ (p2 ∧ False))) ∨ p1)) ∨ (p3 → ((p5 ∨ ((True → ((p5 ∨ p5) ∨ (p3 ∧ p3))) ∧ p4)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225987723763301360749568377936 : (((p3 ∧ p4) ∨ p5) ∨ ((((p2 ∧ True) ∧ (((p4 → p3) ∧ p2) ∧ ((False → True) ∨ ((p4 ∧ ((p5 ∨ p1) → p2)) → p1)))) ∨ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149515928522078571011543967878 : ((p1 ∧ ((p3 ∧ True) ∨ (p1 → (((p2 ∧ p3) ∨ (True → (p4 → p2))) ∨ (((p1 → p3) → p1) → p3))))) ∨ ((p3 → (p1 ∧ p1)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52327530225203121727308269422 : ((((False ∨ ((p1 ∨ True) ∧ (((True ∨ False) ∨ (p1 ∨ p3)) ∨ p4))) ∨ p2) ∧ (p4 → (p5 ∨ ((((False → p2) ∧ p2) → p4) ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133991408927579167147980312502 : ((((((True → p4) → ((p5 ∨ (p1 ∨ (p2 ∧ (p3 ∨ p3)))) ∨ p4)) ∧ ((True ∨ p1) ∧ (p1 → p4))) ∧ True) ∨ True) ∨ (True ∧ (False → True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158898927027900892013529476810 : ((p1 ∨ (((((p4 ∧ (p5 ∨ (p4 → p1))) ∨ p3) ∨ False) ∧ (p5 ∨ ((p2 ∨ False) ∨ False))) → False)) ∨ (p2 ∨ ((True ∨ p1) ∨ (p3 ∧ p2)))) := by
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
theorem thm_5_vars_115025576399768406527629502917 : (((p4 ∨ ((((p5 ∨ False) → p5) → p4) ∨ (p4 ∨ (p5 ∨ p4)))) ∧ (((p3 ∨ True) ∧ (p3 ∧ (p2 → (p1 ∧ p5)))) ∧ p3)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43388860670811901122910006962 : ((((((p3 → (((p5 → False) ∧ p5) ∧ p3)) ∧ ((p3 ∧ p3) ∧ ((p3 ∨ p3) ∨ p2))) ∨ (((p5 ∨ p5) ∨ p4) ∧ p5)) ∨ False) → p5) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h12 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h11
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h13 := h4 h12
          -- We need to get the left conjuct of h13 based on <expert-advice>.
          let h14 := h13.left
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h16 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h17 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h16
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h18 := h4 h17
          -- We need to get the left conjuct of h18 based on <expert-advice>.
          let h19 := h18.left
          -- We need to get the right conjuct of h19 based on <expert-advice>.
          let h20 := h19.right
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h21 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h22 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h23 := h4 h22
        -- We need to get the left conjuct of h23 based on <expert-advice>.
        let h24 := h23.left
        -- We need to get the right conjuct of h24 based on <expert-advice>.
        let h25 := h24.right
        -- One of the premise coincides with the conclusion.
        exact h25
    case inr h26 =>
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h30 =>
          -- One of the premise coincides with the conclusion.
          exact h28
        case inr h31 =>
          -- One of the premise coincides with the conclusion.
          exact h28
      case inr h32 =>
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h33 =>
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149781655260964057546572839419 : ((False ∨ (((((p1 ∨ p2) → (True ∨ p4)) ∨ (p4 → (True ∨ p4))) ∨ ((p3 ∨ p5) ∨ p3)) → (p3 ∨ p5))) ∨ ((p5 ∧ (p5 ∧ p5)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185485926452337023165028052446 : ((p2 ∨ (((p4 → ((p1 ∧ p2) ∨ (True ∨ p2))) ∧ False) ∧ p1)) ∨ (True ∨ ((p2 ∨ (False ∧ p2)) ∨ ((p2 ∨ p2) ∨ ((False → p4) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58147993117076691680531247057 : (((p2 ∧ p4) ∧ (((True ∧ (((p5 ∨ p1) → (((p4 → (p5 ∨ p4)) → (True → p3)) ∧ p2)) ∧ (True ∨ False))) ∨ p1) ∧ (True ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50542774971146554373125311617 : (((((p2 ∨ ((p2 ∨ (p5 → p4)) ∨ p2)) ∧ (((p3 ∨ True) → (True ∧ p4)) ∨ (True → False))) ∨ False) → ((p3 ∧ p2) → (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659042821480543682834394154216 : ((((p2 → (((((True ∨ p2) ∧ p4) → ((False ∨ ((p1 ∨ False) ∨ False)) → p1)) → (p2 → (p4 → (p5 → p3)))) ∧ p3)) ∨ (p5 → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703325844529585685787197443548 : ((((p5 ∧ (True → (((p1 ∨ p2) → (p2 ∧ False)) ∨ p2))) ∨ (((p5 ∧ (((p5 → True) ∨ (p3 ∨ p1)) → (False ∧ True))) ∧ p3) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257488966144217143551826790414 : ((p3 ∨ False) → ((((p4 ∧ (p2 ∧ (p3 ∨ (p1 ∨ p2)))) ∧ (False ∧ ((((p1 ∧ p4) ∧ p5) ∧ p4) ∧ p3))) ∧ (True ∨ (p4 ∨ p5))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300560109088988568920516074945 : (False ∨ (((p1 → (True ∧ p3)) → ((p3 ∧ (True → (((p4 ∧ p3) ∨ p1) ∧ ((p5 ∨ p4) ∨ p1)))) ∨ p4)) ∨ ((True ∨ (p4 ∧ False)) ∨ p5))) := by
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
theorem thm_5_vars_349410586920436716122539607383 : (p3 → (p4 → (((((((False ∧ True) ∨ (p5 ∨ False)) ∨ (p2 ∧ True)) ∨ p5) ∨ (p5 ∧ (p3 ∧ (False ∧ p5)))) ∧ p2) ∨ ((p5 → False) ∨ True)))) := by
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
theorem thm_5_vars_618914502212022226515326760452 : (((((p4 → (True ∧ p5)) ∧ (p5 → (p1 ∧ ((True ∨ (p1 ∨ (p1 ∧ p3))) ∧ (((p3 ∧ p5) → ((True → True) ∨ p4)) → False))))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157622903728568630831062528623 : (((((p2 → (p4 → ((False → p3) ∨ True))) ∧ p3) → (p1 → (True → p2))) ∧ ((p1 ∨ True) ∨ p1)) ∨ ((True ∧ True) ∧ (p1 ∨ (True → True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671522955375992078378858441666 : ((((p3 → (p5 ∨ ((((True ∨ p2) → p5) ∧ (p4 ∧ (((True ∨ p1) ∧ ((True ∧ p4) ∨ False)) ∧ p4))) ∧ p3))) ∨ ((p3 ∨ True) ∨ p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_152647410189581159750471401564 : (((True → p2) ∧ ((p3 ∧ (p5 ∧ p3)) ∨ ((p2 ∨ p3) ∧ ((p5 ∨ ((False ∨ True) ∨ (p1 ∨ p2))) ∨ True)))) → (True → (p3 ∨ (p1 → p1)))) := by
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
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h18
            case inl h19 =>
              -- False on the left can always be used.
              apply False.elim h19
            case inr h20 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h21
              -- One of the premise coincides with the conclusion.
              exact h21
          case inr h22 =>
            -- Disjunctions on the left can always be decomposed.
            cases h22
            case inl h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h24
              -- One of the premise coincides with the conclusion.
              exact h24
            case inr h25 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h26
              -- One of the premise coincides with the conclusion.
              exact h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- One of the premise coincides with the conclusion.
        exact h28
    case inr h29 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h30 =>
        -- Disjunctions on the left can always be decomposed.
        cases h30
        case inl h31 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h32
          case inl h33 =>
            -- Disjunctions on the left can always be decomposed.
            cases h33
            case inl h34 =>
              -- False on the left can always be used.
              apply False.elim h34
            case inr h35 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
          case inr h36 =>
            -- Disjunctions on the left can always be decomposed.
            cases h36
            case inl h37 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
            case inr h38 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h29
      case inr h39 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690141803392803775842847471705 : ((((p1 ∨ ((False ∨ (((p3 ∨ p3) ∧ p4) → p1)) ∨ ((p2 ∨ (p3 ∧ True)) → p3))) ∨ (((p3 ∨ False) ∨ ((p1 ∨ True) ∨ p4)) ∧ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57683370278820532790470217109 : ((((p3 → p4) ∨ p1) → ((p3 → ((p3 ∧ (p5 ∧ p2)) → ((((p3 → p4) → p3) → p1) ∧ (True → ((p5 ∨ p3) ∧ p5))))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50716990273726850549355458657 : ((((p5 ∨ False) ∨ (((((True ∧ p3) → p1) ∨ (p3 → p1)) ∨ (p3 ∨ (p2 ∨ p3))) ∧ (p5 ∧ p5))) → ((False → p5) → (p1 ∨ p5))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h8.left
        let h12 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h8.left
        let h15 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h8.left
        let h19 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Conjunctions on the left can always be decomposed.
          let h22 := h8.left
          let h23 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
        case inr h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h8.left
          let h26 := h8.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_482948104727808334200192080600 : ((((p3 ∧ (p5 → (((p4 ∧ p2) ∧ p4) ∨ True))) → (p2 ∨ (((False ∨ (True → (False → p5))) → (p3 ∧ ((p5 ∨ False) ∨ p1))) ∨ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
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
theorem thm_5_vars_950052653895079817847591730414 : (((((True ∨ p4) → False) ∧ ((((p3 → p2) ∨ p5) ∧ p5) → ((p3 ∧ (p2 ∧ ((p2 ∨ (False ∧ (p2 ∧ p1))) ∨ p4))) ∧ (p2 ∨ p1)))) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_93113590332712372387870934576 : ((True ∧ ((p1 ∨ (p5 ∨ True)) → ((((True → p4) → p1) ∨ p3) ∧ ((p1 ∧ ((p2 ∨ (p1 → (p1 ∧ p1))) → (p1 ∧ p3))) ∨ p1)))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ (p5 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136373711016245683714831978281 : (((((p1 → True) → p2) → p3) ∨ ((((((p2 → ((False ∧ p5) → True)) → p2) ∨ p4) ∨ True) → (False ∨ p3)) ∧ p3)) ∨ ((True → False) → p1)) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700095808074140580936375903375 : ((((((p5 ∨ p5) ∨ p2) → (p1 ∧ ((False ∨ (p3 ∧ p3)) ∨ p1))) → (((p1 ∨ p5) → (p2 → (p5 ∨ ((p1 → p3) ∨ p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179718650991936890330681953960 : (((((p1 → ((p4 ∨ p5) ∨ (True → (p1 ∧ p1)))) ∨ True) → False) ∧ p3) → ((p4 → True) → (p4 ∨ (p5 ∨ ((p1 → p5) ∧ (p3 ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((p1 → ((p4 ∨ p5) ∨ (True → (p1 ∧ p1)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206040539565528934617504033020 : ((p2 ∧ (p4 ∧ ((p4 → p5) ∨ p5))) ∨ ((((p3 ∨ p2) ∨ (False ∧ (p3 ∨ p4))) ∨ (p3 ∨ p5)) ∨ (False → ((p5 ∨ p5) ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47119401481226333619583453423 : ((((False ∨ (((p2 → (p1 ∧ ((p2 ∧ p3) ∧ p2))) → p3) ∧ (p1 ∨ ((p5 ∧ p3) ∨ True)))) ∨ ((p1 ∨ p5) ∧ p3)) ∨ (p5 → p5)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40328429703009361794038688419 : (((((((p2 ∨ ((p2 ∨ (p2 ∧ p4)) ∨ (p1 ∧ ((((p1 ∨ (p5 → p3)) → p3) ∧ p1) ∨ p5)))) → p1) → p5) ∨ True) ∨ p5) ∨ False) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636762359371340597338707738639 : (((((p5 → (((True → p2) ∨ ((p4 → p2) ∨ True)) ∧ (True ∧ (True ∧ False)))) ∨ (False ∨ (p4 ∨ (p5 ∧ (p1 ∧ (p5 ∧ p3)))))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2825466711624476786099533107 : ((((p5 → p4) → True) → p2) → (((((p4 → p1) ∧ (p2 ∧ (((True → False) ∨ False) ∨ (p1 → p1)))) ∧ False) ∧ (p2 → True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 → p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261133311404228217286234916664 : ((p4 → p4) → (((((p4 ∧ (True ∨ (p2 ∨ p2))) ∧ (True ∨ p5)) → (p3 → True)) ∧ ((False ∨ (p5 ∧ (False → p2))) ∧ (True → p5))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654386828521236067660503272445 : (((((((p1 ∧ ((p2 → True) ∨ p1)) ∧ p4) ∧ (((True ∧ p3) ∨ (True ∧ (p2 ∧ True))) → ((p1 ∨ p1) ∨ p3))) ∨ True) ∨ (p3 → p2)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_114135595631597823671142453273 : (((((((p1 → (((p5 ∧ p4) ∧ (p4 → p3)) → True)) → (p2 ∨ p4)) ∧ p5) ∨ (p1 → p5)) ∧ True) → ((p3 ∧ p5) ∨ p1)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63885528854154718177044405359 : ((False ∨ ((((p5 ∨ (True ∧ (p3 ∧ (((True → p1) → (p4 ∧ (p4 ∧ ((False → p2) ∧ (p2 ∧ p2))))) ∧ p4)))) → p2) ∨ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185725761639397105670388979071 : ((p3 → (((((p2 ∧ p4) → p5) ∨ (p2 ∨ False)) ∧ False) ∧ True)) ∨ (p1 ∨ ((p2 → (p1 ∧ (False → ((False → False) ∧ False)))) ∨ (True → True)))) := by
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
theorem thm_5_vars_114867055387655964649160420117 : (((((p5 ∨ (p3 ∨ (p3 ∨ False))) ∧ p5) ∧ (p5 → ((p4 → p1) ∨ p4))) ∨ ((False ∨ (True ∧ ((True → p5) ∨ p5))) ∧ p5)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669794360307217235991895920100 : ((((((p5 ∨ ((p4 → (p5 → (False ∧ p5))) ∨ p2)) → (p2 → (p3 ∨ True))) → (p1 ∨ ((p1 ∧ True) ∧ p5))) ∨ ((p2 → p2) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_348288066875043767075475356790 : (p3 → (True ∧ (p4 ∨ ((p5 ∧ ((p3 ∧ p5) ∨ ((((p3 → p2) ∧ (p1 → p4)) ∧ p2) ∧ p4))) ∨ (p5 → ((False → (p2 ∨ p5)) ∧ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117777833716745694587120107722 : ((p4 ∧ ((p2 → (((False ∧ False) ∨ (True → (((p2 ∨ p5) → (p2 → (False ∨ p2))) ∨ p1))) ∧ p5)) ∧ (p5 ∨ (p4 → p2)))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199492931673011068034904791116 : (((True → ((p3 → (p2 → True)) ∨ p2)) ∨ p5) → ((((False ∧ p5) ∧ p2) ∧ p2) ∨ ((((p2 ∨ (p5 ∧ p5)) → False) → True) ∧ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119652185528320662271257105751 : (((((p3 ∨ ((p2 ∨ (p2 → (p3 ∨ p2))) ∨ ((p2 ∨ (True → (p1 ∨ p5))) ∨ p4))) ∧ (p1 ∨ (p1 ∧ True))) ∧ p3) ∧ p4) → (p2 ∨ p1)) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h16 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- Conjunctions on the left can always be decomposed.
          let h18 := h17.left
          let h19 := h17.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h15
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h21
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h28 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
          case inr h29 =>
            -- Conjunctions on the left can always be decomposed.
            let h30 := h29.left
            let h31 := h29.right
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h7
          case inl h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- Conjunctions on the left can always be decomposed.
            let h35 := h34.left
            let h36 := h34.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h35
      case inr h37 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h39 =>
          -- Conjunctions on the left can always be decomposed.
          let h40 := h39.left
          let h41 := h39.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117267073513029889307033054789 : ((False ∧ ((((p2 → True) → (p5 ∧ (p1 → (p5 ∨ p3)))) ∨ ((False → p2) ∧ ((True → False) ∧ (False ∨ (p1 ∧ p2))))) ∧ p5)) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308679832935267391183937489605 : (p2 ∨ ((False ∨ (((p2 ∨ (False ∧ (False ∧ (True → (p1 → ((p5 ∧ (p2 ∨ True)) ∧ ((p5 → (p5 ∧ p2)) ∧ False))))))) ∨ p5) ∨ True)) ∨ p4)) := by
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
theorem thm_5_vars_175293444697861484950275710432 : ((p3 ∨ (((p3 → False) ∨ p3) ∧ ((p3 ∨ True) ∨ ((False ∨ p3) → (p3 ∧ p1))))) → (p4 → (((True → p1) ∧ (p2 → (False ∨ p4))) ∨ True))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
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
      cases h6
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
theorem thm_5_vars_165113791647069841397882202351 : (((p3 → ((p2 → ((p2 → (False ∨ p3)) ∧ ((p3 → p4) → p3))) ∨ (p5 → p3))) → p1) ∨ (((p2 ∨ p1) ∧ p2) ∨ (p1 ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197422437849011123769349372242 : (((p4 → ((False ∧ (p3 ∨ p1)) → p3)) → False) ∨ ((((False → True) ∧ (((p4 ∨ True) ∨ p3) ∧ False)) ∨ (p4 ∨ (p1 → True))) ∨ (p2 → p2))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_575714739594804790427930980 : ((((True ∨ (((True → (((p4 → p4) → p4) ∨ (((p2 ∧ False) ∧ ((False → True) ∨ False)) ∨ p1))) ∨ p4) → p2)) → True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689076887619216359522675047961 : (((((False ∧ (p2 ∧ ((((p5 → p2) ∨ ((p2 ∧ False) ∨ p3)) ∨ p3) ∧ p5))) ∨ p5) ∨ (False ∧ (((p3 ∨ (False ∧ p4)) ∨ p2) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47391313493744223653591821375 : ((((p2 → p2) → (((p5 ∨ p3) ∧ p1) ∧ (False ∧ (((p1 ∨ ((True ∨ p3) ∨ (p5 ∨ (False ∧ p3)))) ∨ p4) → True)))) ∨ (p1 → p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133668674077049497953891581495 : (((((((p3 ∨ (p4 → True)) → ((True ∧ p5) ∨ p4)) → (True ∨ ((True → True) ∨ p4))) → True) → (False ∨ p5)) ∧ True) ∨ (p1 ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55144834602916132181267983510 : (((((p2 ∧ (p5 ∨ p1)) ∨ False) ∨ p2) ∨ ((p2 → False) → (p1 ∨ (p2 → (p1 ∨ ((((p5 ∧ (p2 ∨ p4)) ∨ True) ∧ p2) ∨ False)))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175359460553863033033496887998 : ((p5 ∨ (p2 ∧ (p4 ∨ ((True ∨ (p3 ∧ (((False → p2) → p4) ∨ False))) ∨ p1)))) → (((False ∨ ((True ∨ (False ∧ False)) → p4)) ∨ p3) ∨ True)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- False on the left can always be used.
            apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219685799128939534838309283928 : ((p1 → ((p2 ∨ False) ∧ p3)) → ((p3 → False) ∨ (((p4 → (p5 ∨ (True → p1))) ∧ (((p2 → p4) ∧ ((True ∨ p2) ∧ p2)) ∧ p1)) → p2))) := by
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
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h11 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114378583077694580024700050307 : (((((p3 ∨ ((p4 ∧ (p2 → True)) ∧ p5)) → ((False ∧ (False ∨ p2)) → (p3 ∧ p5))) → p3) ∨ (True ∧ ((p2 ∧ True) ∨ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262397938167926974084604374624 : (True ∧ (((p1 ∨ p5) → ((((p2 → (True ∧ (p4 ∧ (p5 → (p2 ∨ p2))))) ∨ (p4 ∧ (p2 ∧ p2))) ∨ False) ∧ (p5 → (p3 ∧ p4)))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801743104267766625086827873063 : (((p2 → (((p2 ∧ p5) ∧ p4) ∨ (False ∨ (((p3 ∨ p1) → ((p1 ∨ p1) ∧ False)) → (p4 → ((False ∨ True) ∧ ((p2 → False) → p1))))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118856377010111872944180858268 : ((True → (((((p3 → p5) ∧ (p2 ∧ p4)) ∧ p5) → (p3 ∧ False)) → (((p3 ∧ p1) → ((True → p5) ∧ False)) ∨ (True → p2)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787562442289981301893913314043 : (((p4 ∨ (p1 ∨ ((p5 ∧ False) ∨ ((((((p4 ∧ p2) → p1) ∧ (p5 ∧ (p2 ∧ p4))) → (False ∧ p5)) → p3) → ((True ∨ True) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114964542302880098198669659671 : (((True → (True ∨ (p1 ∨ (((p1 ∨ True) ∨ (p3 ∨ (p3 ∧ p4))) → p3)))) → (p3 ∧ ((True → ((p1 ∨ p3) → p2)) ∧ p3))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256075007578258102879907992450 : ((True ∨ p4) → (p1 ∨ ((p5 → (((p2 ∨ ((p4 ∨ p2) ∨ False)) ∧ True) ∨ ((True ∨ ((p3 → True) ∧ (p5 → (False → True)))) → True))) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_188924438934480616772400645031 : (((p3 ∨ ((p5 ∧ p2) ∨ p3)) → (p1 ∨ (p4 → p4))) ∧ (((True ∧ False) ∨ (((p1 ∧ False) ∧ False) ∨ True)) ∨ ((p3 → (False → p4)) ∨ p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
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
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124943366309203050044428663981 : ((((p2 ∨ p4) → (p5 ∧ p1)) → ((p5 → p2) ∨ ((p3 → ((p2 → p1) ∨ p4)) → (((False ∧ True) → (True ∨ p1)) ∧ p5)))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126627703524049066139971893877 : ((p3 ∧ ((p4 → p1) → (p1 ∧ (((((p5 ∧ ((True ∨ (p3 ∨ p5)) ∧ p3)) ∨ ((False ∨ False) ∨ p3)) ∧ p4) → p2) ∧ p1)))) → (p1 ∨ True)) := by
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
theorem thm_5_vars_133767022074160626220923498090 : ((((p4 → (p1 ∨ ((p5 ∨ p1) ∧ p1))) → ((((p5 ∨ p5) ∧ p4) ∨ ((p3 ∨ p5) → True)) ∨ (p4 ∧ p1))) ∧ False) ∨ (p1 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178680329770744092057399121830 : (((p3 → (p1 ∧ (p5 ∨ p2))) ∧ (True ∨ (False ∨ (p2 ∨ (p5 ∨ p2))))) ∨ (p1 ∨ (((p2 ∨ p3) ∨ (p1 ∨ ((p1 ∨ p5) ∨ True))) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590931855051004388519835276984 : (((((False → (((p1 → p4) ∨ (p2 → p5)) → (False ∨ (p1 → ((p3 ∨ (p2 → (True ∧ (p4 ∧ (True ∨ True))))) ∨ p2))))) → p3) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64039059876545157408993255703 : ((False ∨ (((((p2 ∧ ((p5 → p5) → (p2 ∧ p4))) ∧ ((p1 ∧ p1) → p1)) ∨ (p5 → (p5 ∧ False))) ∨ True) ∨ (p4 ∨ (p4 ∨ False)))) ∨ p1) := by
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
theorem thm_5_vars_111570154199688399924763867972 : (((((p5 ∨ (p2 → False)) ∨ (((p3 → ((((p2 → p2) ∨ p5) ∧ True) → False)) ∨ False) ∧ ((p4 ∧ p3) ∨ p2))) ∧ p2) ∨ False) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191900520632236960870287209781 : ((p5 ∨ (((p2 → (p4 ∨ True)) ∧ p3) ∨ (p2 ∨ p4))) ∨ (((p4 ∧ p3) ∨ (False ∧ p2)) → (((p4 ∨ p1) → (p4 → False)) → (False ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : (p4 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- False on the left can always be used.
    apply False.elim h11
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h16 : (p4 ∨ p1) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h16
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h19 := h17 h18
    -- False on the left can always be used.
    apply False.elim h19
  case inr h20 =>
    -- Conjunctions on the left can always be decomposed.
    let h21 := h20.left
    let h22 := h20.right
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59959336239821788318617336261 : (((True ∨ p4) → (((((p3 → (p3 ∧ p2)) → (p5 ∧ p3)) ∧ (p2 → p1)) ∧ ((p3 ∨ True) ∨ p5)) ∧ (p1 → ((p5 → p1) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115030842897303534718802448534 : (((p3 → ((((p2 → False) → p3) → ((p3 → p4) ∧ p2)) ∨ p1)) ∧ (True ∧ (True ∧ ((((p1 → True) → True) → p5) ∧ p1)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324076948144032334477679442768 : (p5 ∨ (((p1 → (p5 ∧ ((((p3 → True) ∨ False) ∧ p4) ∨ p5))) → p1) ∨ ((p4 ∨ p5) → ((p2 → p2) ∨ (p3 → (True ∨ (p5 ∧ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117357276043670972212719437195 : ((False ∧ (p5 ∧ (p5 ∨ (((((((p4 → ((p2 ∨ p3) → p4)) → True) ∨ False) ∧ p5) → (False ∧ (p3 ∧ p2))) ∨ p2) ∨ p3)))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356024718272918182336397320078 : (p5 → ((((p4 ∨ ((((p3 ∧ True) → p5) → p5) → (p4 ∧ p5))) ∧ (p2 ∧ p3)) ∧ (p2 ∨ (p4 → p1))) ∨ (((p4 ∨ p1) ∧ p3) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56376455366772661771429346841 : (((((p5 ∨ p4) ∧ p3) → p5) → (((False ∨ True) ∨ (p4 → (((p5 ∨ p5) ∨ (p5 → ((True ∨ p1) → False))) ∨ True))) ∧ (p2 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_480679544274709303584770469445 : (((((p5 ∨ (p1 ∧ (p4 → (False → p2)))) → p3) ∨ (((p4 → (((p5 ∧ p3) → p4) ∨ p3)) → True) ∧ ((p2 → p3) ∨ (p1 ∨ True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159036458653577473098306229207 : ((p4 ∨ (True → (False ∨ ((False → p2) → ((True ∨ p2) → ((p2 ∨ (p3 → (p1 ∧ p2))) → p2)))))) ∨ ((p5 ∧ ((True → p5) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111113074065009445839477763897 : (((((((((p4 ∧ False) ∧ False) → p5) ∨ p3) ∧ p4) ∨ p2) → (((p3 ∨ p2) → ((p2 → p5) ∧ p2)) ∧ (p2 → p5))) ∧ False) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138236628222253476947919163184 : ((p2 → ((((p4 ∨ (True → True)) ∨ True) → ((p3 → p2) ∧ p4)) ∧ (False ∧ ((False ∧ (p4 ∨ True)) ∨ (p4 ∨ p5))))) ∨ ((p5 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67895653674331891183751943464 : ((p2 → ((((True → p4) ∧ False) ∧ (p2 ∧ (((p1 ∨ (p5 → (p2 → False))) ∨ p4) ∧ p5))) ∨ (p4 ∧ (((p5 → p1) → p3) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3232625418236355394335562747 : ((p2 ∨ p3) ∨ (((((p5 → ((p5 → ((p4 ∨ p3) ∨ (p4 → ((False ∨ p1) ∧ p2)))) ∨ False)) → p5) ∨ (p3 ∨ True)) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160873418687545013059037370502 : (((((p4 ∧ False) ∧ p2) ∧ p3) ∨ (((p3 → p3) ∧ (p3 ∧ (False → ((p5 → p4) → p3)))) ∧ True)) → (((p3 → (False ∧ p1)) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h5.left
    let h8 := h5.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54259751850342679967367768426 : (((((p4 ∨ (p2 ∧ p4)) ∨ True) → (p2 → p4)) ∧ ((p3 → (p4 ∧ (p5 ∨ p1))) → (p5 ∧ (False ∧ (((p4 → p2) ∨ False) ∧ True))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65313844562328352312355147765 : ((p3 ∨ (((((p1 → ((True ∨ (False ∧ True)) → p3)) ∨ False) → ((((p2 ∨ False) → p4) → p3) ∧ p5)) ∧ True) ∨ ((p2 ∨ p5) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124263486711498123329425067446 : (((False ∨ (((p5 → (p2 → (p2 → p4))) ∨ p5) ∨ p5)) → ((p5 ∧ ((False → (False → p5)) → p1)) → (False ∧ (p5 ∨ p4)))) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140954826040121618852042590470 : ((((p2 → p5) ∨ ((p3 ∨ (p1 ∨ (p4 → True))) ∧ p3)) ∨ (((True ∧ True) ∨ (p1 ∨ (True ∨ (p1 ∨ p4)))) → p4)) → ((p2 ∨ True) ∨ False)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185462383312598545497952549432 : ((p1 ∨ (((((True ∧ (True ∨ p2)) ∧ p5) → p5) ∨ p4) → False)) ∨ (False → ((((True ∨ p4) ∧ p5) → ((p4 ∧ p4) ∧ p2)) → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618446376531194040502483632752 : (((((((p1 ∨ p2) → p3) ∨ p2) → (False ∧ (p3 ∧ (p4 ∨ ((p3 ∨ ((False ∧ p1) ∧ (False → (p2 ∨ (p2 → p2))))) ∧ p3))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



