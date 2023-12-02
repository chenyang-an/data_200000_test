variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118782136536435624259830762442 : ((p5 ∨ (p3 ∨ (p3 ∨ (((p2 ∨ (((((p5 ∨ p4) → p2) ∨ (p4 ∨ False)) ∧ p5) → False)) ∧ (p2 → True)) ∨ (p3 → True))))) ∨ (p4 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168014521749295830237282611994 : ((((p2 ∨ p2) ∧ ((p2 ∧ p5) ∨ False)) ∨ (p1 ∨ (((p5 ∧ (p4 → p5)) ∧ p2) ∧ True))) → ((((p3 ∨ False) → (True → p3)) → False) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
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
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h10 : ((p3 ∨ False) → (True → p3)) := by
          -- Implications on the right can always be decomposed.
          intro h11
          -- Implications on the right can always be decomposed.
          intro h12
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h13 =>
            -- One of the premise coincides with the conclusion.
            exact h13
          case inr h14 =>
            -- False on the left can always be used.
            apply False.elim h14
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h15 := h2 h10
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- False on the left can always be used.
        apply False.elim h16
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h21 : ((p3 ∨ False) → (True → p3)) := by
          -- Implications on the right can always be decomposed.
          intro h22
          -- Implications on the right can always be decomposed.
          intro h23
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h24
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h26 := h2 h21
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- False on the left can always be used.
        apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h30 : ((p3 ∨ False) → (True → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h31
        -- Implications on the right can always be decomposed.
        intro h32
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h33 =>
          -- One of the premise coincides with the conclusion.
          exact h33
        case inr h34 =>
          -- False on the left can always be used.
          apply False.elim h34
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h35 := h2 h30
      -- False on the left can always be used.
      apply False.elim h35
    case inr h36 =>
      -- Conjunctions on the left can always be decomposed.
      let h37 := h36.left
      let h38 := h36.right
      -- Conjunctions on the left can always be decomposed.
      let h39 := h37.left
      let h40 := h37.right
      -- Conjunctions on the left can always be decomposed.
      let h41 := h39.left
      let h42 := h39.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h43 : ((p3 ∨ False) → (True → p3)) := by
        -- Implications on the right can always be decomposed.
        intro h44
        -- Implications on the right can always be decomposed.
        intro h45
        -- Disjunctions on the left can always be decomposed.
        cases h44
        case inl h46 =>
          -- One of the premise coincides with the conclusion.
          exact h46
        case inr h47 =>
          -- False on the left can always be used.
          apply False.elim h47
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h48 := h2 h43
      -- False on the left can always be used.
      apply False.elim h48



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218850554354617620737109528079 : ((p2 ∧ ((True → p4) → p1)) → ((False ∧ ((p5 ∧ p1) ∨ ((p4 ∧ ((True ∨ (p4 ∨ p5)) → p5)) ∨ p2))) ∨ (p4 ∨ ((p2 → p4) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h5
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149030677773598071974718422465 : (((True ∧ (p3 ∨ p3)) ∨ (((True ∧ ((True ∧ (p1 → ((p2 ∧ (p1 → p3)) ∧ False))) ∨ p4)) ∨ p5) → False)) ∨ ((p1 ∧ True) → (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_166542158996308793477774178987 : ((p5 ∨ ((((p3 → (p4 ∧ p5)) ∧ (p3 → ((p4 ∧ (p3 ∨ p2)) ∧ p3))) ∧ p4) → False)) ∨ (True ∨ ((p2 → ((p2 ∧ p1) → p3)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157038386444000691452272880546 : ((((p4 → False) → (p1 ∧ (p1 → ((p4 ∧ (((p5 → p3) ∨ p3) ∧ (p4 ∨ p3))) ∨ p2)))) ∨ True) ∨ (((p4 ∧ True) ∧ False) ∨ (p1 ∨ p3))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116803630503004460936669295475 : (((p3 ∨ False) ∨ (((p2 → False) → (((p1 ∧ p4) ∨ p2) ∨ ((p3 ∧ False) → (False → (p4 ∨ ((p3 ∨ False) ∨ True)))))) → p3)) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660385540889143438743699627057 : (((((False → ((((((p1 ∧ (False ∧ p5)) ∨ p5) ∨ (True → (True ∨ p2))) ∧ (True → True)) ∧ (p4 ∨ False)) ∨ p1)) ∨ p1) → (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171056445700486094806662967187 : ((p5 ∨ (((p1 ∧ ((p4 ∨ p5) → ((p5 ∨ True) ∨ False))) → (p4 ∧ False)) ∨ True)) ∧ (((p3 → p4) ∧ (True → ((True → p4) ∨ True))) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151333427047210434023026519258 : (((p1 → (((p3 → (p5 ∨ ((p4 ∨ (p3 ∧ True)) ∧ False))) ∨ p4) ∨ (((False → p1) ∨ p5) ∨ p3))) → False) → ((p2 ∧ p2) ∧ (p3 → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 → (((p3 → (p5 ∨ ((p4 ∨ (p3 ∧ True)) ∧ False))) ∨ p4) ∨ (((False → p1) ∨ p5) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 → (((p3 → (p5 ∨ ((p4 ∨ (p3 ∧ True)) ∧ False))) ∨ p4) ∨ (((False → p1) ∨ p5) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h6
  -- False on the left can always be used.
  apply False.elim h9
  -- Implications on the right can always be decomposed.
  intro h10
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : (p1 → (((p3 → (p5 ∨ ((p4 ∨ (p3 ∧ True)) ∧ False))) ∨ p4) ∨ (((False → p1) ∨ p5) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h12
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h11
  -- False on the left can always be used.
  apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617784486672275455313319607628 : (((((p3 → (((p4 → p3) ∧ p4) → p2)) ∨ ((False → True) → ((p1 ∨ (p2 → False)) → (p2 ∨ ((p2 ∨ p5) → (p3 → p3)))))) ∨ p1) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598762627907633142626028148604 : (((((p1 ∧ True) ∧ (((p5 → False) ∨ False) → ((False ∧ (True → p5)) ∨ (p5 ∨ (p2 → ((((p2 ∨ p3) ∨ False) → False) → True)))))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326803464896874805642661436991 : (True → ((p3 → ((p3 ∧ (p3 → (((True ∧ False) ∧ p3) ∨ (((p5 ∧ p5) ∨ (False → ((p4 ∨ False) → (p5 ∧ True)))) → p4)))) ∨ p3)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302776234151530101403017969253 : (False ∨ (p4 ∨ ((p4 → p2) → ((p3 ∧ (p3 ∧ (False ∧ ((((True → p3) ∨ p5) ∨ False) ∨ p2)))) ∨ (p2 → (((p3 ∧ False) ∧ True) → False)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41692611556284400851742161675 : (((((p1 → ((True ∨ p2) ∨ p3)) ∧ p5) → ((False ∨ ((p5 → p5) ∧ (((p2 ∨ True) → (p4 → p2)) ∨ (p4 → True)))) ∧ True)) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134205512192935856062551160138 : ((((((p3 → True) → (p1 ∧ (p5 ∧ p2))) → False) ∧ (((p2 ∧ ((p3 ∧ p3) ∨ (True ∧ p3))) ∨ False) → p5)) ∨ p1) ∨ ((p1 ∨ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_489814359461988914272453525852 : (((((True ∨ True) ∧ (p5 → True)) ∧ ((p3 ∧ ((p2 → (((p3 → p4) → (p2 ∧ (p3 ∨ ((p4 ∧ False) ∨ p4)))) ∧ p4)) ∧ p1)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18083052222810233961920589909 : (((p1 ∨ ((((True ∧ p3) → (p4 ∧ (False → (p1 ∧ False)))) ∨ False) → (p5 → (p3 ∧ (p4 ∨ True))))) ∨ ((p4 ∨ p4) → (False → p1))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49119237010716140515543200307 : ((((((p1 ∨ p5) ∧ p5) ∧ ((((True → p1) → False) ∧ p2) ∧ (p2 ∨ p4))) → (p1 ∧ (p3 ∨ (p4 ∨ p3)))) ∨ ((p3 ∧ p2) → p3)) ∨ p3) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731912190042720919136492778358 : ((((p5 → (p5 ∧ p3)) → ((p3 → p4) ∨ (((p5 ∧ ((p2 → (p2 ∧ False)) ∨ ((p2 → p4) → (p3 ∧ p5)))) → False) → (p3 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306578666712917792212026399521 : (p1 ∨ ((p4 ∨ p2) → (((True ∧ (False ∧ (((p2 → (False ∨ p1)) ∧ (p4 ∨ p4)) → (p2 ∨ ((p3 → (p5 → p4)) ∧ False))))) ∨ p4) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185314859070557385203698674659 : ((p3 ∧ ((p1 → ((p3 → ((p1 → p2) ∧ p5)) ∧ p5)) → p2)) ∨ (p5 → ((False ∨ (p5 ∨ p4)) ∨ (p1 ∧ ((p4 ∧ (p4 ∨ p4)) ∧ p4))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347811307073710093390766235997 : (p3 → ((p4 → (False ∨ p2)) ∨ (((False → (True ∨ p2)) → (p1 ∧ (p4 ∧ False))) → (((((p4 ∧ p3) ∨ p2) → p5) ∧ p5) ∨ (p5 ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (False → (True ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261209346508732319502455870760 : ((p4 → p5) → ((((((p1 ∨ p1) → p3) → ((p3 ∨ (False ∨ (True ∨ (p4 ∧ False)))) ∨ (p1 ∨ True))) ∨ p5) → False) → ((p2 ∨ p1) ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 ∨ p1) → p3) → ((p3 ∨ (False ∨ (True ∨ (p4 ∧ False)))) ∨ (p1 ∨ True))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : ((((p1 ∨ p1) → p3) → ((p3 ∨ (False ∨ (True ∨ (p4 ∧ False)))) ∨ (p1 ∨ True))) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h6
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199041805588506385516054666236 : (((((p5 ∧ (p5 ∧ p5)) → True) ∨ False) ∧ p4) → (((p5 → p2) ∧ p2) ∨ (((True ∨ ((p2 ∧ ((True ∧ False) ∨ True)) → p5)) → p1) ∨ p4))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119034539205013316818054089031 : ((p1 → (((p4 ∧ ((((p3 ∨ p4) → ((False ∧ p5) ∧ p2)) → ((True → False) ∧ True)) → ((True ∧ p2) ∨ p2))) ∨ p2) ∧ p2)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638240970363348032904788645388 : (((((p1 ∨ ((p2 ∧ (True → p4)) → (p1 → p2))) → ((p2 → (False → p2)) → ((True → p5) → ((p4 ∧ True) ∨ (p3 → p4))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159352870185403402142056100826 : (((((p5 → ((p2 → True) → p2)) → (p3 → (((True ∧ p4) → p3) ∧ (False → p2)))) ∧ p5) ∧ p3) → (True → ((p1 ∨ (p5 → p2)) ∨ True))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54558018973587652189604076339 : (((p3 ∧ (((p5 ∨ p5) ∨ (p4 ∨ p5)) → False)) ∨ ((p5 ∨ p3) ∨ ((((((p5 ∨ True) ∨ p5) ∨ (p2 ∨ p4)) ∧ False) ∧ True) → p5))) ∨ p3) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h5
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675991090752656827686555860633 : (((((((False ∧ ((p5 → p5) ∨ p4)) ∧ p1) ∨ p1) ∨ (p5 → (p4 ∨ (p3 → ((p1 ∧ p3) → p5))))) ∧ ((p4 ∨ (p4 → False)) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746025269472147432252217126135 : ((((p1 ∨ True) → ((((False ∧ False) ∧ (((p4 ∧ (False → p2)) ∨ (((p1 ∨ p4) → p3) ∧ (False → (p2 ∧ False)))) ∧ p2)) → p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218243943972932826474613457991 : (((True ∨ p3) ∨ (p5 ∨ p2)) → ((((True ∨ p3) ∨ (p3 ∨ True)) ∨ (p3 → p2)) → ((True → ((False ∨ True) ∨ ((p4 → p2) ∧ p4))) ∨ p4))) := by
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
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h6 =>
          -- Disjunctions on the left can always be decomposed.
          cases h6
          case inl h7 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h8
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h9 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h10
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h13
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h14 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h15
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h17 =>
          -- Disjunctions on the left can always be decomposed.
          cases h17
          case inl h18 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h19
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h21
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h24
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h25 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h26
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h29 =>
          -- Disjunctions on the left can always be decomposed.
          cases h29
          case inl h30 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h31
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h32 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h33
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h34 =>
          -- Disjunctions on the left can always be decomposed.
          cases h34
          case inl h35 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h36
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h37 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h38
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h39 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h40
          case inl h41 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h42
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h43 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h44
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h45 =>
          -- Disjunctions on the left can always be decomposed.
          cases h45
          case inl h46 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h47
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h48 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h49
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h50 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h51 =>
      -- Disjunctions on the left can always be decomposed.
      cases h51
      case inl h52 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h53
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h54 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h55
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h56 =>
      -- Disjunctions on the left can always be decomposed.
      cases h56
      case inl h57 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h58
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h59 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h60
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177268745388998370444145418939 : ((False ∨ (p1 ∨ (False ∨ (((p3 ∧ (True ∨ p3)) → (True ∨ False)) ∨ p3)))) ∧ (((p3 ∨ (p2 → p2)) ∨ False) ∧ ((p3 ∧ p1) ∨ (p1 → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299980465724870814483997742709 : (False ∨ ((((p5 ∧ ((((False → False) → p4) ∧ False) ∧ (p3 → ((False → p5) ∨ p5)))) ∧ p3) ∨ ((p4 → True) ∨ (p4 ∧ p4))) ∧ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_594653887234490387398436992272 : (((((((p1 ∧ (((((p3 ∧ p2) → p2) → True) ∧ (p2 ∨ p1)) → True)) → p3) → True) → (p3 → ((p3 → p3) → (False ∨ p5)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55763055171285401437399586951 : ((((False ∧ p4) ∧ (p4 ∨ True)) ∧ (p3 → ((((p2 → (p4 ∨ True)) → (((p2 ∨ ((p4 → p3) → p1)) ∧ p5) ∨ True)) → True) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689276819438678176261402012376 : (((((((((p5 ∧ (p3 ∧ (p4 ∧ p4))) → False) ∨ p3) → p2) ∧ True) ∧ (p3 ∧ False)) ∨ ((((p2 ∧ (p3 → p4)) ∧ True) ∧ p2) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649182757119548414672112216678 : ((((((p5 → (p2 ∨ p3)) ∧ ((((p3 ∨ p5) → (((p1 ∧ p5) ∧ True) ∨ p2)) → (p2 → p3)) → (p2 ∧ p5))) → p5) ∧ (False ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156602342937012715309810854495 : ((((((True → p3) → (((p1 ∧ p4) → False) ∧ (False ∨ p1))) → (False ∨ (p1 ∧ p4))) ∧ p4) ∧ p1) ∨ (((p1 → p1) ∨ False) ∨ (p3 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355562161382052297889562134417 : (p5 → (((((((((p2 ∨ p5) ∨ ((p3 ∨ (p2 → p3)) ∧ False)) ∧ (True ∨ False)) ∨ p4) ∧ p3) ∧ False) ∧ p3) ∨ (p2 → p4)) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637930476007482568973534741521 : (((((p2 ∨ (((p4 → (p3 ∨ False)) ∨ False) ∧ p1)) ∧ ((((p1 ∧ (p4 ∧ p5)) ∨ p4) ∧ p3) → (p3 ∨ (p1 ∧ (False → p2))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149154540085379068787930011439 : (((p1 ∨ p4) ∧ ((((((p1 ∧ True) ∧ ((p5 → p5) ∨ p4)) → p3) ∧ (p3 ∧ p5)) ∧ p1) ∨ (False ∨ p1))) ∨ ((p4 → p2) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41368084015416723401699264075 : (((((((p5 ∧ p1) → p3) → False) ∨ (p4 ∨ (p2 ∨ ((p3 ∧ True) ∧ (True ∨ p4))))) → (p3 ∨ ((p3 ∧ p2) ∧ (True ∨ False)))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185271557614417710775747164054 : ((p1 ∧ (p4 ∨ ((p4 ∨ (((False → False) ∨ p4) → False)) ∨ p5))) ∨ (True ∨ ((((p2 → p5) → p2) → (p4 ∧ ((True ∧ p4) ∧ p1))) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186605626044701601599056713672 : (((((p4 ∨ p1) ∨ (p2 → True)) ∨ (p1 ∧ False)) → (p3 ∨ p3)) → ((p2 ∨ p5) ∨ ((p5 ∨ (True ∧ p2)) → ((p3 ∧ True) ∧ (False ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (((p4 ∨ p1) ∨ (p2 → True)) ∨ (p1 ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h12 : (((p4 ∨ p1) ∨ (p2 → True)) ∨ (p1 ∧ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h12
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h17 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h18 =>
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45485855798049874566785492381 : (((False ∨ ((p1 ∧ (False → True)) ∨ (((((p2 → (False ∨ (True ∧ p5))) → (((p2 → p4) → p1) ∨ p4)) ∧ p3) → True) → p3))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805276353401309262152792253610 : (((p3 → (p5 ∧ ((((((p1 ∨ p5) ∧ p5) → ((((p5 ∨ (p3 → (True → (p5 ∨ True)))) ∧ True) ∨ p4) ∨ p4)) ∧ p2) ∨ p2) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62827238021877751389249585520 : ((p4 ∧ ((((p1 ∨ (p4 ∧ p2)) ∨ (p5 ∧ False)) ∧ p1) ∧ (((p5 ∨ ((p4 ∧ False) → False)) → ((p3 ∧ p1) ∨ p4)) ∧ (p3 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729376144677386884795997689768 : (((((p3 ∧ p1) ∨ p1) → ((((p2 ∧ (p4 ∧ (p3 → p4))) ∨ p3) ∧ p2) ∨ (((True ∧ False) ∧ True) → (((p5 ∧ p4) ∨ p5) ∨ p3)))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- False on the left can always be used.
    apply False.elim h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179478997362646933337728821868 : ((True → (((p3 ∨ (True ∨ False)) → (p5 → (False ∧ p2))) → (p5 ∧ False))) ∨ (False → (p4 ∧ ((False ∨ (True ∧ (p5 → True))) → (p2 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54985566473644738871421539785 : ((((False → p3) ∧ (p1 ∧ (True → p3))) ∧ ((False ∨ False) ∨ (p5 ∨ ((((p1 ∧ False) → p4) → (p2 ∧ ((False ∨ p5) ∧ p3))) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259295399237623913964979258932 : ((False → p1) → (p3 ∨ (((p5 → p4) → (p1 → (((p5 → p3) ∨ (p4 → p4)) ∨ (False ∧ ((p1 ∨ (p5 ∨ p5)) ∨ True))))) ∨ (True → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50185897741511868602139877612 : (((((((p4 ∨ True) ∧ False) → False) ∨ (((False ∧ (False ∧ (p2 ∧ p5))) ∧ (True ∨ True)) → p3)) ∧ p2) ∨ (p1 ∧ (p4 ∧ (p2 ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208868075449396866268876148637 : ((p4 ∧ ((p5 ∧ p3) ∧ (p5 → p3))) → ((p1 ∧ (((p1 ∧ p3) ∧ (True → p1)) ∧ ((p1 ∧ (p1 ∧ (p2 → p1))) ∧ p1))) ∨ (p4 → p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193936993765663514712912702433 : ((p2 ∨ ((((p4 ∧ p5) → (p2 ∧ p4)) ∧ p4) ∨ p1)) → (((p3 ∧ ((True ∨ (p2 ∧ (p1 ∨ p2))) ∨ p2)) ∧ p2) ∨ (p1 ∨ (False → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177999066432808094185340569350 : (((p1 ∨ ((p1 → ((p2 → (p3 → (p2 ∨ p3))) → p4)) → False)) ∨ p1) ∨ (p2 → (((True → (p2 ∧ (p2 ∧ (p3 → p3)))) ∨ p2) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707428880668169259553728751410 : ((((((True ∧ p2) ∨ p1) ∧ (p2 ∨ (p3 ∨ p4))) ∨ (((p2 ∧ ((False ∧ p2) ∧ (p3 → (p4 → ((p3 ∨ p5) ∧ True))))) → p1) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_67540078063873668665517067256 : ((p1 → (((p5 → p3) → False) ∧ (((p1 → ((((p1 → ((p5 → p1) ∨ p4)) ∧ False) ∧ p2) ∨ (p2 ∨ p3))) ∧ (p3 ∧ p2)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243944790474969233793296127241 : ((True ∧ p1) ∨ (((((p1 → True) ∧ (((((p1 → ((False → p2) ∨ p1)) ∧ (p1 ∨ p4)) ∧ p2) ∧ p2) → (p3 ∧ p2))) ∨ False) ∨ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134659478239583538622863105352 : (((((((p5 ∧ ((p3 ∨ p4) ∧ p5)) → p3) ∨ p3) ∨ p4) ∨ (False → ((p4 ∨ p2) ∨ (p5 ∨ (p5 ∨ p5))))) → p5) ∨ (True ∨ (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139782323798617660020232927063 : (((False ∨ (True ∨ ((p1 ∧ (((p4 → ((p5 ∧ p3) ∧ ((p5 ∨ p3) ∧ (True ∨ p2)))) ∨ p5) ∨ p3)) → p5))) → p1) → ((p5 ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37087021884235755234723772376 : ((((((False ∧ (False ∨ p1)) ∧ ((((p1 ∨ p4) ∧ p4) ∨ (True ∧ ((True → (p5 ∧ (p5 ∧ p3))) ∨ p1))) ∧ False)) ∨ True) ∧ p4) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184005623029211831647772899428 : ((((((p5 ∧ ((p4 → False) ∧ True)) ∨ p1) → False) ∨ p1) ∨ False) ∨ (p4 ∨ ((True ∨ p4) → (True ∨ (p3 ∨ (p2 → ((False ∨ p3) ∧ p4))))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193076752299113548092241659310 : ((((p3 ∨ (True ∨ p4)) → p3) ∧ (p4 ∨ (False → p5))) → ((((p5 ∨ True) ∨ p2) ∨ p4) ∧ ((p4 ∨ (p2 ∨ p3)) ∨ ((p4 ∧ p5) → False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h10 : (p3 ∨ (True ∨ p4)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h11 := h6 h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729864950864524032377124712939 : (((((p1 ∧ p1) → p1) → (p4 ∨ ((False ∨ (((p4 → p4) → p4) ∨ ((((p5 ∧ p1) ∨ (False → (p2 → p5))) ∨ p2) ∨ p4))) ∧ True))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135488279428760515521585697149 : ((((p1 ∨ True) ∧ ((True → p4) ∧ (((p2 ∨ (p3 ∧ (False → p3))) ∧ True) ∧ (p5 ∨ p1)))) → ((p5 → p2) → p1)) ∨ (p4 → (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185560627649568190945531416607 : ((p4 ∨ (((p5 ∧ True) ∧ True) ∧ (((p3 ∨ p3) → p2) → p5))) ∨ ((((False ∧ (p2 ∧ p5)) → (p4 ∧ True)) → (True ∨ (p5 ∧ p5))) ∨ p5)) := by
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
theorem thm_5_vars_695429998096410864552199182591 : (((((((((False ∨ p3) ∧ True) → True) ∧ p2) ∧ (p5 → p1)) ∨ (False ∧ p5)) → (((p2 → (p1 ∧ p5)) ∧ (False → (p5 → p2))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154714758906430436656633554523 : (((((p3 ∧ (p3 ∨ (((False ∨ p2) ∧ p2) ∨ (p4 ∧ True)))) ∧ (p5 ∧ p5)) ∨ True) ∨ (p1 ∨ p3)) ∧ ((True ∧ False) → (p5 ∧ (p5 ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51522986254292089985884292360 : ((((p1 → p3) ∨ ((((p4 ∨ p4) ∨ (False ∧ (p5 → p1))) ∨ (p2 → (p1 ∨ p3))) ∧ p5)) → (((p4 → (p2 → p5)) ∨ False) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639468466957395560977347654232 : ((((((p5 ∧ True) ∧ p3) ∧ (((p2 ∧ (p4 ∨ p4)) ∨ ((p1 → ((True ∧ (True ∨ p2)) ∧ ((p4 ∨ p1) → False))) ∧ p1)) ∧ True)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133654751354846023857093908204 : (((((((p3 → (p5 → p2)) → (p2 → (((p4 ∧ (p3 ∨ False)) ∨ False) → False))) → p2) ∨ p1) ∨ (p4 ∧ p4)) ∧ p3) ∨ (p2 → (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614745924380885671860088619660 : ((((((((p5 → ((p5 → False) ∨ p2)) ∨ p5) ∧ ((False → False) ∧ True)) → (p1 ∨ (p5 ∧ False))) ∨ (((p1 ∧ True) ∨ p1) ∧ False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_257410802778666360280479022331 : ((p2 ∨ p5) → (False ∨ (p2 ∨ (p4 ∨ (((p3 ∨ (p1 → (True ∧ (p1 ∨ (True ∧ ((((p3 ∧ p3) ∧ True) ∧ False) → p4)))))) ∨ p2) ∨ p1))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336282281022396294055239750570 : (p1 → (((((p3 → p3) → ((p2 ∨ p5) ∨ p1)) → (p2 ∨ p4)) ∨ (False → ((p2 → False) ∧ ((p2 → p5) ∧ ((p3 → p2) ∧ p5))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592953882475034655949620241807 : (((((p2 ∨ (False ∧ (p5 → (((((True ∧ p2) → (p5 ∨ p5)) ∨ (p2 ∧ True)) ∨ True) → (True ∧ False))))) ∧ ((p3 ∧ p4) ∨ p1)) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800938645216286104240655183983 : (((p2 → (((True → (p2 ∧ False)) ∧ (p5 → ((p4 → p4) → ((p3 ∧ (p3 → (False ∨ True))) ∧ ((p4 ∧ True) ∨ False))))) → (p1 ∨ p5))) ∨ p2) ∧ True) := by
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616208236707532233243928001840 : (((((True ∨ (p3 → (((p1 ∨ p1) → p2) → (p5 ∨ (True → p4))))) ∧ (False ∧ (p2 → ((p1 → p5) ∧ (p5 ∨ (p5 → p3)))))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207590746701156627016850290411 : (((((p1 ∧ True) ∧ False) → p1) → False) → (False ∧ ((True ∧ (p4 ∨ (p5 ∨ ((p5 ∧ (True ∨ p1)) ∧ (((p1 ∨ False) ∨ p3) ∧ p3))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∧ True) ∧ False) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258204370178224567881881246107 : ((p4 ∨ p4) → (p5 ∨ (p1 → (p2 → ((((p3 ∧ ((True → True) → True)) ∨ ((p5 ∨ (False → (p2 ∨ False))) → False)) ∧ (p1 ∨ True)) ∨ True))))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177751524011659545310269448301 : ((((p1 → p1) ∧ (p3 ∧ ((p2 → p3) ∧ (p1 → (p3 ∧ False))))) ∧ p2) ∨ (p5 → (p1 → (p3 ∨ ((True ∧ p1) ∨ ((p4 → p1) ∨ p3)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169525771841329597032978978468 : (((p5 ∧ (((p2 ∨ (True ∧ (((p2 → p3) ∧ False) ∨ p5))) → p1) → p5)) ∨ True) ∧ (False → (False ∧ (((p3 ∧ p4) ∨ (p5 ∧ p4)) → p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740303664793770982324231263452 : ((((p1 ∨ False) ∨ (p1 ∨ (p4 ∧ (p1 ∨ (((p3 → ((p3 ∧ True) ∧ (p3 ∧ (p1 ∧ p5)))) → (p4 → (p4 ∨ (p3 ∧ p5)))) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137641210418795383791997315769 : ((False ∨ ((((((p2 ∨ (True ∨ p1)) ∧ p3) → p3) → False) ∧ p5) ∧ (p2 ∨ ((p5 → (p5 ∧ (p3 ∨ False))) → p1)))) ∨ ((False ∧ p4) → False)) := by
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
theorem thm_5_vars_648491073799874117405105559543 : (((((((p2 ∧ ((False ∧ p1) ∧ p3)) ∨ (p4 ∨ ((p3 → ((False ∧ p2) → p4)) → (True ∧ True)))) ∨ (p1 ∧ p2)) ∨ p1) ∧ (True ∨ p2)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172285736287169436413803900168 : (((p5 ∨ ((True ∨ p4) ∧ (p3 ∨ (p3 ∧ p3)))) ∨ ((p5 → (p4 ∨ p2)) ∨ True)) ∨ ((p2 → (((p4 ∧ (p3 → p4)) ∧ p4) ∧ p5)) → p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707337232404068542335683027369 : (((((p3 ∧ ((p3 ∨ p3) → p4)) ∨ (p4 ∧ p1)) ∨ ((p2 ∧ (p1 ∧ ((((p1 → ((p4 → False) ∧ p4)) → p3) ∧ p1) ∧ p3))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_779494106901672329569967816069 : (((p2 ∨ (((((False → (p1 ∨ p3)) → p5) ∧ (p1 ∨ (False → p1))) ∨ (p4 ∨ (((p3 → (p5 → (p4 ∨ p5))) → p1) ∨ True))) ∨ p2)) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171422594391906428603713714250 : ((((False ∨ p3) ∧ (p3 ∨ (p4 ∨ ((p5 ∨ (True ∨ p4)) → (p1 → p4))))) ∧ p4) ∨ (p2 → (False → ((p5 ∨ (False → (p3 ∧ True))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193115711849594969739590301148 : ((((True ∨ (p3 ∧ p4)) ∧ True) ∨ (p3 → (p4 → p4))) → (True → ((((p4 → p4) ∧ (p2 ∨ p5)) ∨ False) ∨ (((p5 ∨ True) ∨ p4) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315640746659973751829097106220 : (p3 ∨ ((True ∧ p4) ∨ (((((p3 ∨ ((p4 → p3) ∧ p2)) ∧ (p2 ∧ p4)) ∨ ((p4 ∨ p1) → (p4 → p4))) ∨ (p4 ∧ (p5 ∨ p2))) ∧ True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173052423096897073468342184724 : ((False ∨ (((p5 ∧ p5) ∨ ((p3 → ((p3 ∧ (p1 ∧ False)) → True)) ∨ p3)) → p2)) ∨ (((p2 ∨ (False ∨ p4)) ∨ (True ∨ (p5 → p5))) ∨ p2)) := by
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
theorem thm_5_vars_181478393557213063336007583215 : ((p4 ∨ (p2 ∧ ((p2 ∧ (((p3 ∧ p3) ∨ (p4 ∨ p5)) ∧ p1)) ∧ p3))) → (p3 → ((((True ∧ p4) ∧ p5) ∨ True) ∨ ((p3 → False) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301421823284351738598712753246 : (False ∨ (((p4 ∨ (True → False)) → p1) → ((p1 → p5) → (((p2 → p1) ∧ True) → (p4 → ((p5 ∧ ((False → (False ∧ False)) → p4)) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (True → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158762235526046418581569876613 : ((p4 ∧ (((True ∨ p2) ∨ p5) ∧ (((p2 → ((p1 ∧ False) → (p5 ∨ p5))) → p3) ∨ (p3 ∧ p2)))) ∨ ((((p1 ∨ p1) → True) ∧ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757860826214396764499981191326 : (((p1 ∧ (p3 ∨ ((((((((p4 → True) ∧ ((p4 → p1) → p3)) ∧ p1) ∧ True) ∧ (p1 ∨ (p1 ∧ p2))) ∧ (p2 ∨ False)) ∧ p4) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113554394024227368368829864194 : ((((p5 → (p1 ∨ p4)) → (((False ∧ True) ∧ (p2 ∨ ((False ∨ p1) → p3))) ∨ ((p5 ∨ p2) ∧ (p2 ∨ p3)))) ∨ (p5 ∨ p2)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62017403297860833078278540112 : ((p2 ∧ (((p3 ∨ p5) ∧ p4) ∨ ((False ∧ (((p1 ∧ True) ∧ (p5 ∨ p2)) → (False → ((p1 → p1) ∧ p4)))) ∨ ((p3 ∨ p5) → True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158337718165178260564874652403 : (((p2 ∧ True) ∧ (True ∧ ((((p2 ∧ (p5 ∨ (p2 ∧ False))) → p3) → p5) ∧ ((p5 → False) → p5)))) ∨ (p3 → ((False ∧ False) → (True ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60806460676584964432417006569 : ((True ∧ (p2 ∧ (((p2 ∧ ((p3 ∨ p4) ∧ ((p5 ∧ p4) ∨ p4))) ∨ ((True → p2) → p5)) → (p5 → (p2 → ((p5 ∧ p3) ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



