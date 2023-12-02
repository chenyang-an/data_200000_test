variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41176482987051957745856021485 : ((((((((((p2 ∧ p1) ∧ (p4 ∨ p2)) ∨ False) → (p2 ∧ p4)) ∨ (p2 ∨ p1)) ∧ (p4 → False)) → True) → (p1 → (p5 ∨ p5))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757495395091700280195048478043 : (((p1 ∧ (False ∧ (p5 ∧ (p5 ∨ (p5 ∧ (p4 → ((p5 ∨ (p4 ∧ p2)) → ((((p2 → p5) ∨ ((p4 ∧ p1) ∨ p1)) → p3) ∨ True)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172240706071865107275746229664 : (((((p3 ∧ (p4 → p1)) ∨ p4) → (False ∨ p4)) ∧ (p2 ∧ ((p2 ∨ False) → True))) ∨ (((True → True) ∧ False) → (p2 ∨ (p4 ∧ (p4 ∧ False))))) := by
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
theorem thm_5_vars_227733736383609426372530514841 : ((p1 ∧ (False ∨ p1)) ∨ ((True ∨ p2) ∧ ((p4 ∨ (((False ∨ (((p4 ∧ True) ∨ False) ∧ False)) → (p5 ∨ p5)) → p3)) → ((False ∧ p4) ∨ True)))) := by
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
theorem thm_5_vars_208596867134543311497257867551 : (((p3 → True) → (False → (p3 ∧ p5))) → (((p5 → (p4 → ((p5 ∧ p2) ∧ p2))) ∨ ((p3 → ((False ∨ p2) → p3)) ∧ (False → p4))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63932937284337473884797431512 : ((False ∨ ((((p5 ∧ p3) ∧ (((p5 ∨ p2) ∧ ((True ∨ p1) ∨ p2)) ∧ (p4 → (((p1 ∨ p5) ∧ p5) ∧ p1)))) ∨ (True → True)) ∨ p3)) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161893793301612576972822011307 : ((False → (p2 ∨ (p5 → (((p5 → p1) → (True ∧ (p4 → ((p5 ∧ False) ∧ (p3 ∨ p3))))) → p3)))) → ((p5 ∨ ((p2 ∨ p5) → False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862779253328618814790330020838 : (((((p2 ∨ (p1 ∨ (p5 → ((p3 → p4) → ((p5 → (p3 → (False ∨ p3))) → False))))) ∨ ((p5 → True) ∨ ((False ∧ False) ∨ True))) → False) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∨ (p1 ∨ (p5 → ((p3 → p4) → ((p5 → (p3 → (False ∨ p3))) → False))))) ∨ ((p5 → True) ∨ ((False ∧ False) ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
theorem thm_5_vars_659810949418303733128471807288 : (((((p2 ∨ (((((p2 ∨ ((p4 ∧ True) ∧ True)) → ((p3 ∧ True) ∨ p3)) ∧ p5) ∨ False) ∧ (p4 ∨ (p5 → p4)))) ∧ True) → (p2 ∨ p3)) ∨ p3) ∧ True) := by
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
  cases h2
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h11 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : (p2 ∨ ((p4 ∧ True) ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h11
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h15
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
        have h19 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h18, we can now drive its conclusion.
        let h20 := h18 h19
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h21 : (p2 ∨ ((p4 ∧ True) ∧ True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- One of the premise coincides with the conclusion.
          exact h20
          -- True on the right can always be proven directly.
          apply True.intro
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h22 := h9 h21
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59035818157162304229761145181 : (((p4 ∧ p1) ∨ ((p1 ∨ (p2 ∨ ((((((p5 → (p1 → p4)) ∨ p4) ∨ p2) → p5) → p5) → (p2 ∨ ((p2 ∧ p4) → p2))))) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42951255017855425620776816440 : (((p4 → (False ∨ (((p2 ∨ (((p3 → ((p3 ∨ False) ∨ (p5 → p3))) → p1) ∨ (p1 → ((p4 ∧ p2) ∧ True)))) ∨ True) ∧ p1))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129222847162787434982893555028 : ((((p3 ∨ ((p2 ∨ (p1 ∨ (p4 ∨ p4))) ∨ (p1 → (False → p2)))) ∧ ((False → p3) ∨ (p3 → (p2 ∧ p1)))) ∨ p1) ∧ (True ∨ (p1 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253796586477779173601216705079 : ((p1 ∧ p2) → ((p3 ∨ ((((p3 ∨ (True ∨ p5)) → (p4 ∨ p4)) → p2) ∧ ((p5 ∨ p5) ∧ ((p5 ∧ (p3 ∧ p3)) ∨ p2)))) ∨ (p1 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39343187193020716891928510447 : (((p2 ∧ (p2 ∧ (((((p5 ∧ (((p3 ∨ (p3 ∨ ((True ∧ p4) → False))) ∨ p2) ∨ p5)) ∧ (p1 ∨ p2)) ∨ p5) → p5) → p2))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183463794769707532610924024311 : ((p2 ∨ (p4 ∨ ((((p4 → False) ∧ (p5 ∨ False)) ∨ False) ∨ True))) ∧ (((False ∧ (True ∧ True)) ∧ False) → ((True → (p2 ∧ p2)) ∨ (p1 → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138066639205586636465629216491 : ((True → (True → ((p2 → ((((((True ∧ p5) → False) ∨ p3) ∧ (p5 ∧ p4)) ∨ ((p3 → False) → p2)) ∧ True)) ∧ p1))) ∨ ((p2 ∨ True) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317850910457113117643792071846 : (p4 ∨ (((p5 ∧ p5) ∧ ((False ∧ p5) ∨ (True ∨ (((p1 ∧ (p2 → p3)) → ((p1 → (((p4 → p4) ∧ p2) ∧ p1)) → p2)) → p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118154857724157998232283634907 : ((False ∨ ((((p1 ∨ p2) ∨ p4) → True) ∧ (True → (((p1 → p5) → ((p3 ∧ (p3 ∨ p4)) ∧ p4)) ∨ ((p1 ∧ p3) ∧ p4))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140503291055074762278238049830 : (((((p1 → (True ∨ False)) ∨ p1) ∧ (((p4 ∧ (p3 → False)) ∨ (p2 → p5)) ∨ p4)) ∧ (((False → p5) ∧ True) → p3)) → ((True → p1) → p1)) := by
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
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h12 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h13 := h2 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h19 := h2 h18
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263516658718788550666061358958 : (True ∧ (((p4 ∨ (p4 ∨ (False ∨ (p4 ∧ (((p5 → True) ∧ (p2 ∧ (p2 ∨ p4))) ∨ False))))) → (False ∨ True)) ∧ (p3 → ((p4 ∨ p2) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
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
          -- False on the left can always be used.
          apply False.elim h17
  -- Implications on the right can always be decomposed.
  intro h18
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200433910098974266068852982890 : (((p3 ∨ p2) ∨ (True ∨ ((p3 → False) → False))) → (((((False ∨ (False → True)) → True) → p5) → (p4 ∨ p2)) ∨ (((p4 → p1) ∨ p4) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
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
theorem thm_5_vars_308370705592039316564474919020 : (p2 ∨ (((((((p2 ∨ p3) → (p5 ∨ (p2 → ((((p2 → p5) ∧ p5) ∨ p5) ∧ (False ∧ p3))))) ∨ (p3 ∧ p5)) ∨ False) ∨ p4) ∨ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180813435888300053172146678945 : ((((p3 ∨ p1) → False) ∧ (p4 → ((False ∧ (p2 → p2)) ∧ (p2 ∨ p2)))) → (p1 → (p5 ∧ ((False ∨ ((p3 → (p1 → False)) → p5)) ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h9 : (p3 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h10 := h7 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232984157019007460464465759559 : ((p3 ∧ (p3 → True)) → ((p5 → p1) ∨ (((p1 → False) → (((p4 → p3) → (p1 → (((True → p3) → p4) → p3))) → p2)) ∨ (p3 ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52859184309307405014625575503 : (((True ∧ (False → (p2 ∧ (False ∧ ((True → (p3 ∨ (p1 → p1))) ∧ p2))))) → ((((True ∨ (p3 → (p5 ∧ p2))) ∨ True) → p5) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_62945439777784417973039604978 : ((p4 ∧ (p4 ∧ (p1 ∨ ((p2 ∨ False) ∨ (((p1 ∧ (((p2 → ((p1 ∧ (False ∧ (p2 ∨ False))) ∧ p3)) → p1) → p1)) ∨ p5) → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_31577606204782063670939094526 : ((False ∨ ((((p4 ∧ ((False → (False ∨ True)) ∧ p2)) ∨ (p4 ∧ (p1 ∧ p2))) ∨ (p4 ∨ ((p5 ∨ ((p4 ∧ p4) → p4)) ∨ p3))) ∨ p4)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42719998410781097711486231392 : (((p5 ∨ (p2 → (((((p4 → ((False ∧ ((True ∨ (p1 ∧ p3)) ∧ False)) ∨ p2)) → p1) ∧ False) ∨ p3) ∨ (p2 → (p2 ∨ p2))))) ∨ p4) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111436480033094147152111885176 : (((p5 ∨ ((((((p4 ∧ (True ∨ (p2 ∧ p5))) ∧ False) → (p2 → (p5 → (False → p5)))) ∧ (p5 ∧ True)) ∨ p4) → p4)) ∧ p1) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713215645343347950164151231357 : ((((p2 ∨ ((p3 ∨ p5) ∧ (True ∨ False))) ∨ (((False ∧ p4) ∨ ((p2 ∧ ((((p3 ∨ (p5 ∧ p1)) → p2) ∨ False) ∨ False)) → p2)) ∨ p2)) ∨ p3) ∧ True) := by
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
      exact h2
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194038489158163007077970877696 : ((p5 ∨ (((True ∨ (False ∨ (False ∨ p4))) ∨ p3) → False)) → (p1 → (((p2 ∨ p2) ∧ ((False ∧ True) ∨ (((p2 ∨ p3) ∨ p4) ∨ p3))) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h14 =>
              -- One of the premise coincides with the conclusion.
              exact h14
            case inr h15 =>
              -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
              have h16 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h15, we can now drive its conclusion.
              let h17 := h15 h16
              -- False on the left can always be used.
              apply False.elim h17
          case inr h18 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h19 =>
              -- One of the premise coincides with the conclusion.
              exact h19
            case inr h20 =>
              -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
              have h21 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h18
              -- We have shown the premise of h20, we can now drive its conclusion.
              let h22 := h20 h21
              -- False on the left can always be used.
              apply False.elim h22
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
            have h26 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h25, we can now drive its conclusion.
            let h27 := h25 h26
            -- False on the left can always be used.
            apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h29 =>
          -- One of the premise coincides with the conclusion.
          exact h29
        case inr h30 =>
          -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
          have h31 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h28
          -- We have shown the premise of h30, we can now drive its conclusion.
          let h32 := h30 h31
          -- False on the left can always be used.
          apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h34 =>
      -- Conjunctions on the left can always be decomposed.
      let h35 := h34.left
      let h36 := h34.right
      -- False on the left can always be used.
      apply False.elim h35
    case inr h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h37
      case inl h38 =>
        -- Disjunctions on the left can always be decomposed.
        cases h38
        case inl h39 =>
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h41 =>
              -- One of the premise coincides with the conclusion.
              exact h41
            case inr h42 =>
              -- We want to use the implication h42 based on <expert-advice>. So we show its premise.
              have h43 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- True on the right can always be proven directly.
                apply True.intro
              -- We have shown the premise of h42, we can now drive its conclusion.
              let h44 := h42 h43
              -- False on the left can always be used.
              apply False.elim h44
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h1
            case inl h46 =>
              -- One of the premise coincides with the conclusion.
              exact h46
            case inr h47 =>
              -- We want to use the implication h47 based on <expert-advice>. So we show its premise.
              have h48 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h45
              -- We have shown the premise of h47, we can now drive its conclusion.
              let h49 := h47 h48
              -- False on the left can always be used.
              apply False.elim h49
        case inr h50 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h51 =>
            -- One of the premise coincides with the conclusion.
            exact h51
          case inr h52 =>
            -- We want to use the implication h52 based on <expert-advice>. So we show its premise.
            have h53 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h52, we can now drive its conclusion.
            let h54 := h52 h53
            -- False on the left can always be used.
            apply False.elim h54
      case inr h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h56 =>
          -- One of the premise coincides with the conclusion.
          exact h56
        case inr h57 =>
          -- We want to use the implication h57 based on <expert-advice>. So we show its premise.
          have h58 : ((True ∨ (False ∨ (False ∨ p4))) ∨ p3) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h55
          -- We have shown the premise of h57, we can now drive its conclusion.
          let h59 := h57 h58
          -- False on the left can always be used.
          apply False.elim h59



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199143339964911364887126936413 : ((((True ∧ p3) ∨ (False → (False ∨ p2))) ∧ p4) → ((((p1 → (False ∨ (((p3 ∧ False) ∧ (p2 ∧ p4)) ∨ False))) ∨ (True ∨ p5)) ∨ False) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43736788304024240964522563153 : (((((p4 ∨ p4) ∨ (p3 ∨ (p4 → ((p5 → (p4 ∧ (False → p2))) ∨ (((True → p4) ∧ p1) → (p1 → (p1 ∨ p5))))))) → True) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_162841877732307209335277484153 : ((((((p5 → ((p1 ∧ True) ∧ ((p1 ∧ p1) → False))) → p4) ∨ p2) ∨ p3) ∨ (p1 ∨ True)) ∧ ((False ∨ (True ∨ (p5 ∧ p5))) ∧ (False → p4))) := by
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
theorem thm_5_vars_54674742512591402892360156973 : (((((p5 → (p4 ∨ (False → p1))) ∨ True) → True) → ((p4 ∧ ((((p4 → True) ∧ (p2 → p5)) ∨ False) ∧ (p3 ∨ (p3 ∨ p3)))) ∨ True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37770355860203458610745565204 : ((((((True ∨ p2) ∨ p4) → ((p2 ∧ False) ∨ ((((p2 → p4) ∧ ((p3 ∨ (False → False)) → (p3 → p5))) ∨ p1) ∧ p5))) → p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117081999734903146102240014633 : (((False → p2) → ((((p1 ∧ True) ∨ p1) ∨ (((True ∧ p1) → ((True ∧ (p2 ∨ p4)) ∨ (p4 ∨ (False ∧ p1)))) → False)) ∧ p1)) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192058320777950234110229988555 : ((p3 → (((((p4 ∨ p4) ∨ p2) → p4) ∨ True) → p4)) ∨ ((p2 → (True → p2)) ∧ (((((True → p5) ∨ p5) ∨ (p5 → p3)) ∧ p1) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678747040066296658320090463285 : (((((p2 ∨ True) → (p2 → ((((p3 ∨ False) ∧ (p3 ∧ p3)) → (p3 ∧ ((p2 ∧ p3) ∧ p2))) → p1))) ∨ ((False ∨ (False ∧ p4)) → p1)) ∨ False) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38401053040285769788942075270 : ((((p4 ∨ (p3 ∧ ((p1 → p1) ∧ (((p4 → ((False ∧ p2) ∧ p2)) → p1) ∧ p2)))) → ((p4 ∧ (p5 ∧ (p5 → p2))) ∧ True)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20233260637268145149294060295 : (((((((p4 → p2) → p2) ∨ True) ∨ p1) ∧ ((p5 → p4) ∨ (False ∧ p4))) ∨ (((p1 → p4) ∨ True) ∨ ((True → (True → p5)) → p2))) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318987434561366853518995053104 : (p4 ∨ ((((p1 → (((p2 ∨ p4) ∧ p1) ∨ p1)) → (((p5 ∨ ((p4 ∧ False) → p3)) ∧ p5) ∧ False)) → p3) ∧ ((True ∨ (False ∧ p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((p2 ∨ p4) ∧ p1) ∨ p1)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40241328427010312232116181458 : ((((p4 ∧ (p4 ∧ (((((p3 ∧ (p1 → p2)) ∧ (True → p5)) ∧ (p5 ∨ ((p2 ∨ True) ∧ p3))) ∧ p2) → (False ∨ True)))) ∧ p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69216538901516367450708278781 : ((p5 → ((False → (True → (p4 ∨ (p2 ∧ p3)))) ∧ ((p4 → ((p4 ∧ ((p2 → ((p2 ∨ (p5 ∨ p1)) ∨ p3)) → p1)) ∧ True)) ∨ p5))) ∨ p1) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44785265968175752404739233852 : (((((p1 ∧ p4) ∧ True) ∧ (p3 ∧ ((p3 ∨ ((p2 → p1) ∧ p5)) → ((((p2 ∨ (p3 → p3)) ∨ (False ∨ p4)) ∧ p3) ∨ True)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204871362246165656520509238362 : ((((p5 ∧ (p1 ∨ p2)) → True) → p2) ∨ (((((True → False) → p3) ∧ p2) ∧ p1) → ((p4 ∨ (((p5 ∨ (False ∨ p2)) → p2) ∧ p4)) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187304253574637189894676384773 : ((p1 ∧ (((p1 ∧ (p5 → (p5 → p3))) → True) ∨ (True → False))) → (False ∨ ((((False ∨ True) → (p1 → ((p5 ∨ False) ∨ p5))) ∧ p4) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191771082807806957713681321206 : ((p1 ∨ (((p1 ∨ p3) ∧ (p4 ∧ p3)) ∨ (False → p3))) ∨ (((((p1 ∧ (p4 ∨ (p1 ∨ p1))) ∨ False) → (p5 → p1)) ∧ p5) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338036094344548723510941050205 : (p1 → (((p3 ∧ (((p2 → False) → p5) ∧ p5)) ∧ (p3 → p1)) ∨ ((((((False ∨ True) ∨ (True ∨ True)) → False) ∨ False) ∧ (p4 ∨ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53608601470647219357120407676 : (((((p3 ∧ ((True ∨ p3) ∧ p1)) ∧ True) ∨ (True ∨ p4)) ∧ (True ∧ (p5 ∧ (p4 ∨ ((False ∧ p2) ∨ (p5 ∧ ((p3 ∨ False) → p1))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178781557516489749608427029699 : (((p5 ∨ (False ∨ p3)) ∧ ((((p2 ∧ p1) ∧ p3) → (p3 ∨ p1)) → p5)) ∨ (True ∧ (((p1 ∧ ((p3 ∨ p1) ∨ p5)) ∧ (p4 → p3)) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171688596059105615015266700507 : (((p5 ∨ ((p2 ∨ ((p1 → (p4 ∧ True)) ∧ ((p1 ∨ p1) ∧ p1))) ∧ p5)) ∨ p4) ∨ ((((p4 → True) ∨ False) ∧ p5) → (p1 → (True → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_211296508752610711001771286227 : (((True ∨ p1) ∨ (p1 ∧ True)) ∧ (((((((p1 ∧ p4) ∨ (p5 ∧ p4)) → False) ∨ p2) ∨ (p2 → True)) → (p3 ∧ (True ∧ p2))) ∨ (p4 → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149252893337968405862634116015 : (((p2 ∨ p5) ∨ ((((False ∨ p4) ∧ (True ∨ ((p3 ∨ True) ∧ p5))) → (p3 ∧ ((p4 ∨ p2) ∧ p4))) ∧ p1)) ∨ ((True ∨ True) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67724302667489303481233262738 : ((p2 → (((p4 ∧ (p1 → (True → (((p1 ∨ False) ∨ (False ∨ p4)) → (p5 ∧ False))))) ∧ (p5 → ((p3 ∧ (p5 ∧ False)) ∧ p3))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51116959101566814447411623655 : (((((p1 → (p1 ∧ (p3 ∨ (((p5 ∧ ((p2 ∧ p4) ∧ p1)) → p5) ∨ p4)))) → p5) ∨ True) ∨ (False ∨ ((p2 → p1) ∧ (True → p4)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66276592298423906209630088533 : ((p5 ∨ (((False ∨ True) → False) → (((p4 → ((True → ((p4 ∨ ((True ∧ p1) ∨ p4)) ∧ p2)) ∧ (True ∧ p1))) → p4) ∧ (True → p1)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150033707379316672593358705988 : ((p5 ∨ (p1 ∧ (((p2 → p3) → ((p2 ∧ (((p1 ∨ p2) ∧ p2) ∧ p4)) ∨ p4)) ∨ ((p1 → p5) ∨ False)))) ∨ (((p4 → True) ∨ p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112861003798581177363205170847 : ((((p2 ∧ (False ∧ False)) ∨ ((p3 ∨ (((True ∨ True) ∨ p2) → (((p4 ∨ p1) → ((p5 ∨ p2) ∧ True)) → p4))) → p3)) → False) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49089241468726791681265223223 : ((((True ∧ (p4 ∧ (False ∨ (((p1 ∧ (p2 ∨ p5)) → p4) ∨ (False ∧ (p1 ∨ True)))))) ∧ (p4 ∨ (p5 → p1))) ∨ ((p3 ∨ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757788687800741220596971617472 : (((p1 ∧ (p1 ∨ ((True ∨ ((p3 → True) ∧ ((False ∧ ((False ∨ p3) ∧ (p3 ∨ False))) → (((True ∨ True) ∧ p1) ∨ (p3 ∧ p5))))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260100051457908171622305848750 : ((p2 → p1) → ((((((p3 ∧ p5) → (True → p2)) ∧ (p3 ∧ ((False ∨ ((False ∧ p1) ∨ p1)) ∧ False))) ∨ (False → p1)) ∨ (p2 ∧ p2)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57457892980611218442502188838 : (((p5 ∨ (p1 → p3)) ∨ (True → (((p4 ∧ True) ∨ (False ∧ ((((True ∨ p4) ∨ p2) ∨ ((p2 → p4) ∧ p3)) ∨ p3))) ∧ (False → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197535797645967458157997645383 : (((((True ∧ p3) ∧ p3) ∨ False) ∨ (p4 → p2)) ∨ ((((False ∨ (p4 ∨ (p1 ∧ p5))) ∨ False) ∧ p1) ∨ (False → (((p3 → p2) → p4) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67865123244766981996710553941 : ((p2 → ((((True ∧ ((False ∧ p3) ∧ True)) ∨ ((p4 ∧ p4) ∨ ((p4 ∧ p2) ∧ ((p2 ∨ p5) ∧ p4)))) ∨ False) ∨ (False → (p2 ∨ True)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48641748617742618173955836080 : ((((p2 ∨ ((p5 ∧ ((p4 ∨ True) → (True → (True ∨ True)))) → (False → (p3 → p3)))) → (p3 ∨ (p5 ∧ p2))) ∧ (p3 ∧ (p2 ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43601663653753751950801732797 : ((((((True ∧ ((((False ∧ (p4 ∧ (p2 → p4))) ∨ (((p5 ∨ False) → (True ∨ False)) → p5)) → p1) ∨ p4)) ∧ p3) → p5) → p5) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112694005874464205265494392886 : (((((p1 → ((p2 → False) ∧ ((((p4 ∧ p4) ∨ False) → (p4 → p4)) ∧ p4))) ∨ p5) ∨ (((p2 ∨ p4) ∨ False) ∧ True)) → p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60838234598075921681019401672 : ((True ∧ (p1 ∨ (((False ∨ (False ∧ (((p2 → False) ∧ False) ∧ ((((True ∧ (p2 ∨ p2)) ∨ p4) ∨ False) → (True ∧ p3))))) ∨ p1) ∨ True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617766977102759208517053985136 : (((((p4 ∨ ((p4 → p1) ∧ (p5 ∨ p3))) ∨ ((p4 ∧ (p5 ∧ True)) → (False ∨ (False ∨ ((p1 ∧ p1) ∨ (p4 → (p2 → p5))))))) ∨ False) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51291104083299950059241279994 : (((p4 ∧ (p2 ∧ (True ∧ ((((p2 → p1) ∨ ((p2 ∧ (p1 ∨ p2)) ∨ p1)) ∧ p5) → False)))) ∨ (p2 → (((p1 → p3) ∨ p2) → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115672112806524414053797153498 : ((((p5 ∨ p2) → ((p1 ∨ p3) ∨ p2)) ∨ ((p1 ∨ ((p5 ∨ (p4 ∨ ((p4 ∧ p2) ∧ p5))) → p4)) ∨ (p4 → (p1 → p4)))) ∨ (True → p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53953031027787455098654550613 : (((p5 → (p4 ∧ (p2 ∧ (((p3 ∨ p1) ∧ p4) ∨ p1)))) ∨ (p3 → ((False ∨ (False ∨ (False → p4))) ∧ (p4 → ((p1 → True) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158304208760589419251347078939 : ((((p5 → p5) → True) → (((False → p4) ∨ (False → ((False ∧ (p3 ∨ p1)) ∧ p3))) → (p1 ∨ False))) ∨ ((False ∧ (p3 → p2)) → (p3 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791181732713915994142757984870 : (((True → (((p4 → False) → (((((True → True) → ((p3 ∧ p4) ∧ p3)) ∧ p2) → p4) → (p2 ∨ (((True → p4) ∨ p4) ∧ p3)))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353190709927952612810028945461 : (p4 → (p4 ∧ ((False ∧ (((p2 ∧ ((True ∧ (p3 → p2)) ∧ p3)) ∨ p5) ∨ True)) ∨ ((True → ((p2 → (p5 → True)) ∧ p5)) → (p5 ∨ p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306535542046674575486742499567 : (p1 ∨ ((p3 ∧ p4) → ((False ∨ (p1 ∧ ((p2 ∧ (False ∨ ((True → (p1 → False)) → p3))) → (False ∨ False)))) ∨ ((p1 → True) ∧ (True ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347401586010272280800051611039 : (p3 → ((((p5 ∧ ((p5 ∨ p5) ∨ p5)) → p5) ∨ p1) → ((p5 ∧ (p3 ∨ (((p3 → (p3 ∨ p3)) ∧ (p4 → True)) ∨ p2))) → (p4 ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126814503519624730875748360919 : ((p5 ∧ ((p1 ∧ (True → ((p4 ∧ (True → ((p1 ∧ ((p1 ∨ p1) ∧ p5)) ∨ p4))) ∧ (p1 → (False ∧ p3))))) ∧ (p5 ∨ p5))) → (p3 ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h16 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h17 := h7 h16
    -- We need to get the right conjuct of h17 based on <expert-advice>.
    let h18 := h17.right
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h19 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h20 := h18 h19
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- Conjunctions on the left can always be decomposed.
  let h22 := h1.left
  let h23 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h24 := h23.left
  let h25 := h23.right
  -- Conjunctions on the left can always be decomposed.
  let h26 := h24.left
  let h27 := h24.right
  -- Disjunctions on the left can always be decomposed.
  cases h25
  case inl h28 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h29 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h30 := h27 h29
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h33 := h31 h32
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- False on the left can always be used.
    apply False.elim h34
  case inr h35 =>
    -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
    have h36 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h27, we can now drive its conclusion.
    let h37 := h27 h36
    -- We need to get the right conjuct of h37 based on <expert-advice>.
    let h38 := h37.right
    -- We want to use the implication h38 based on <expert-advice>. So we show its premise.
    have h39 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h26
    -- We have shown the premise of h38, we can now drive its conclusion.
    let h40 := h38 h39
    -- We need to get the left conjuct of h40 based on <expert-advice>.
    let h41 := h40.left
    -- False on the left can always be used.
    apply False.elim h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230737331042469274181799742748 : (((p5 → p2) ∧ p2) → ((p2 ∨ p5) → (((p5 → (False ∨ False)) ∨ ((p5 → (p3 ∧ p2)) → (p2 ∨ p1))) → (True → (p3 ∨ (p2 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h1.left
      let h11 := h1.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h13 := h5 h12
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h1.left
      let h19 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h1.left
      let h22 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_787075045841681217190305030309 : (((p4 ∨ ((p4 ∨ p5) ∨ (p1 → (p1 ∧ (p3 ∨ (p5 ∧ (((p1 ∨ (p3 ∨ ((p1 ∨ p1) → p5))) ∨ True) ∨ (False → (False → p1))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354036487958789071155146927249 : (p4 → (p4 → ((p1 ∧ (p1 ∧ (((p5 → (p3 ∨ p1)) → ((p5 ∨ p1) ∨ p1)) ∨ ((p5 ∧ p3) ∨ p2)))) ∨ (False → (p2 ∨ (p1 ∨ False)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172820200488800723514795948218 : ((True ∧ (((False ∧ p1) ∨ (p2 ∧ p5)) ∨ ((False ∨ (True ∨ p3)) ∨ (True ∨ p2)))) ∨ (p2 ∨ (((((p4 → True) ∨ p3) → False) ∨ p5) ∧ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702636667745191314074403057972 : (((((p5 → ((p5 ∨ p2) ∨ ((p5 → p1) ∧ True))) → p4) ∨ ((p3 ∨ (((((p5 ∨ p4) → (p5 ∨ False)) ∧ True) ∧ True) ∨ p4)) ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_115546722667023285693362409003 : (((p3 → (p5 ∨ ((p1 ∧ (p3 ∧ p5)) → p4))) → (((p4 ∧ ((p1 → p5) ∧ (False ∧ (True ∨ True)))) ∧ p3) ∧ (p3 ∧ p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147992218119245933730374665958 : ((((p3 ∨ ((p5 ∧ ((p1 → True) ∧ (True ∨ ((p3 ∨ (p2 ∨ p3)) ∨ p2)))) ∧ True)) ∨ p5) ∨ (p1 ∨ p4)) ∨ (False → ((p1 ∨ False) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157454247567827079887760019846 : (((((p4 ∨ ((p1 → ((False ∨ (p4 → (p1 → p3))) ∧ p2)) ∨ p4)) → False) ∧ p1) ∨ (True ∨ p3)) ∨ (p1 ∧ (p4 ∨ ((True → p1) ∧ p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773549533939776038410543281438 : (((False ∨ ((((p5 ∧ p1) ∨ ((p2 ∨ p3) ∨ (p2 ∧ p5))) ∨ (((True ∨ p2) → (((p4 ∧ p3) ∨ p1) ∨ (True ∧ True))) ∨ p1)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313968689698740983539292741409 : (p3 ∨ (((p2 ∨ ((((False ∨ p3) ∧ (p3 ∨ p3)) → (p2 → False)) ∧ (p1 ∨ (p5 ∨ p3)))) ∨ (p5 ∧ ((p1 ∧ p3) ∨ p1))) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191287031903551184852556168059 : (((p5 ∨ p1) ∧ (((False ∨ p5) → (False ∨ p1)) ∧ p1)) ∨ ((p5 → (p1 ∧ (((p5 ∧ p1) ∨ p3) ∨ p5))) → (((p5 → p2) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185432539955605104221292167841 : ((False ∨ (((p2 ∧ ((p5 ∧ (p3 → p2)) → p5)) ∨ False) → p5)) ∨ (((False ∨ (False ∨ p5)) ∧ ((p2 → True) → p3)) → (p3 ∨ (p3 ∧ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h8 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h9
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h8
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303129394816530518559844798187 : (False ∨ (p3 → ((p1 → (p4 ∨ ((p1 ∨ p5) ∧ (p4 ∨ p5)))) ∨ (((True ∨ p2) ∨ (p3 ∧ True)) ∨ ((p4 → (True ∨ (p1 ∧ False))) → False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_68801492018040405497481857837 : ((p4 → (((p3 ∨ p1) → (True → p3)) ∧ (((((p2 ∨ p3) → (p1 ∨ (p3 ∨ p1))) ∨ (p2 ∧ True)) ∨ p3) ∧ ((False ∧ True) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703030965858389911199365362244 : (((((p4 ∧ p5) ∧ ((p5 ∧ (p3 → (p3 ∧ True))) ∨ False)) ∨ ((((((((False → p2) ∨ p4) ∨ p3) → p3) ∨ p2) → True) ∧ p3) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119095837955182930226266307342 : ((p1 → ((p3 ∨ (p5 → (p1 ∨ (p5 ∨ (p4 ∧ p5))))) → ((((p2 → ((p2 ∨ p4) ∧ p2)) → p1) → (p1 ∧ p2)) ∧ True))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49086143346198723495378700028 : (((((p1 → (((p5 ∧ (p3 ∨ p2)) ∧ ((p4 → (p4 ∧ True)) ∧ p3)) ∨ p3)) → p5) ∧ (p2 → (p2 → p1))) ∨ ((True ∨ p1) ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168178284422338967986733619326 : (((p3 ∨ (p1 ∧ p3)) ∧ ((p1 → ((((True ∨ p4) → False) ∧ (True ∧ True)) → p1)) ∨ p4)) → (p4 ∨ (((p2 ∧ True) ∧ p5) ∨ (p2 ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174616862193165276483378588033 : ((((False ∧ (True ∨ p3)) ∨ p2) → ((p3 → ((p4 ∧ False) ∧ p4)) ∨ (p4 ∧ False))) → (((p2 → p5) → p5) ∨ (False → ((True → p1) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64351669414323506954336436210 : ((p1 ∨ (((True ∧ (p5 ∧ (((((p3 → p5) ∨ p2) ∨ (((p5 ∧ p1) ∧ (p1 → p5)) ∨ p3)) ∧ (p5 ∧ p1)) ∧ p5))) ∨ p1) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316883419844119007116141039170 : (p3 ∨ (p1 → ((False ∨ (p3 ∨ True)) → (p2 → ((False → p3) ∧ (((p5 ∨ False) ∨ p1) ∧ ((p4 → (p5 ∨ p2)) ∧ ((p5 ∨ False) → True)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h9
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Implications on the right can always be decomposed.
  intro h14
  -- True on the right can always be proven directly.
  apply True.intro



