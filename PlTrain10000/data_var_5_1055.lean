variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601300415122847278578578718530 : ((((p2 ∧ ((p1 ∧ ((False → ((p4 → p2) ∧ p4)) ∨ p3)) ∨ (((True ∧ (p4 → (p5 ∨ (p4 ∧ True)))) ∨ (True ∨ p1)) ∧ p4))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151554173457333431454040750197 : (((((p3 → ((False → p2) ∨ (p3 ∧ False))) ∨ ((p5 → (p5 ∧ (p2 ∨ p4))) → p4)) ∨ p5) → (False ∨ p2)) → ((p4 → (p5 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644418741048515624811151383012 : ((((False ∨ (True ∨ (((p4 ∨ ((p3 ∧ ((p2 → ((((p2 → p3) ∨ p2) ∨ p4) ∧ p4)) ∨ (p2 ∧ p4))) ∧ True)) → p4) → p3))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155689705060670624176537063786 : (((p1 ∨ p3) ∨ ((p2 → (False ∨ (((False ∧ (p4 ∧ False)) ∧ ((p5 ∧ p5) ∨ p3)) ∨ True))) ∨ False)) ∧ ((p2 ∨ (p3 ∧ (p2 ∧ True))) → p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762887651635449755965295221994 : (((p3 ∧ ((p3 ∧ (False ∨ ((p2 ∧ p5) ∨ p1))) ∨ ((p5 ∨ p3) ∧ (p3 ∨ ((p5 → (True ∨ (False ∧ p2))) ∧ ((p4 ∧ p4) → p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217316101312445413039743076694 : (((True ∨ (p2 ∨ True)) ∨ True) → (p5 ∨ (p1 ∨ (False → (p3 ∧ (p5 → (((True ∧ p2) → p4) ∧ (p3 ∨ (False → (p2 → (False → p3))))))))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h4
      -- False on the left can always be used.
      apply False.elim h4
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h11
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h11
        -- False on the left can always be used.
        apply False.elim h11
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- False on the left can always be used.
        apply False.elim h17
        -- Implications on the right can always be decomposed.
        intro h18
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h17
        -- False on the left can always be used.
        apply False.elim h17
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h23
    -- Implications on the right can always be decomposed.
    intro h24
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h23
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65029996061565121244600693359 : ((p2 ∨ ((p4 ∧ p3) → ((((p4 ∨ p3) ∧ p1) → (((p2 ∧ True) ∨ p4) ∧ ((p1 ∨ (p3 ∨ (p4 → (p1 → p2)))) → False))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194041438370761024465170683402 : ((p5 ∨ (((False ∧ (p5 ∨ p3)) ∧ p5) ∧ (p5 ∧ p4))) → (((p1 → False) → (True → ((p5 → p3) ∨ (((True ∨ True) ∧ p4) ∧ False)))) ∨ p5)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724472022744316552978542242735 : ((((True ∨ (p3 → p2)) ∧ (((((p5 → (p1 ∧ p5)) ∧ (((p2 ∧ (p2 ∧ p5)) ∧ ((True ∨ p5) → p3)) ∨ p1)) → p1) ∨ True) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317961611016541054000138972149 : (p4 ∨ ((True → ((((True ∨ (p2 ∧ p4)) → (((p3 ∨ p5) ∧ p3) ∧ (False ∧ p4))) ∧ p4) → ((((p5 → p5) ∨ p3) ∨ p5) → p3))) ∨ p3)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h2.left
      let h7 := h2.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h8 : (True ∨ (p2 ∧ p4)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h9 := h6 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h2.left
      let h14 := h2.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (True ∨ (p2 ∧ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h19 := h16 h18
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- We need to get the left conjuct of h20 based on <expert-advice>.
    let h21 := h20.left
    -- False on the left can always be used.
    apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157899253999214795417821265914 : (((((((False ∧ p5) → p4) ∧ p5) ∨ (p2 ∧ False)) ∨ False) → ((p3 ∨ (True ∨ p3)) ∧ (p1 → p2))) ∨ (p4 → (((False ∨ p4) ∧ p4) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606405328748526652501131133767 : ((((((((True ∨ p2) → False) ∨ (p2 ∨ (((((True ∧ True) → p3) ∧ (p5 ∨ p2)) → (p3 ∨ (p4 ∧ True))) ∧ p1))) ∨ p2) ∧ False) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_408242264938581812072900930364 : ((((((((True ∨ (False ∧ (p1 ∧ (True → True)))) ∨ p2) ∨ ((p5 → p4) → p3)) ∧ ((p3 ∨ p3) ∧ p4)) ∨ ((p5 ∧ p5) ∧ False)) → p3) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h4.left
          let h9 := h4.right
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- One of the premise coincides with the conclusion.
            exact h10
          case inr h11 =>
            -- One of the premise coincides with the conclusion.
            exact h11
        case inr h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- False on the left can always be used.
          apply False.elim h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h4.left
        let h17 := h4.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h20 =>
      -- Conjunctions on the left can always be decomposed.
      let h21 := h4.left
      let h22 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h23 =>
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- Conjunctions on the left can always be decomposed.
    let h28 := h26.left
    let h29 := h26.right
    -- False on the left can always be used.
    apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48674954989601808130786461645 : ((((True ∧ (p3 → ((p2 ∧ p1) ∨ ((False ∧ True) ∨ p2)))) ∧ ((p5 ∨ ((p2 → (p1 → True)) ∧ p5)) ∨ p1)) ∧ ((p4 → True) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40142838896270654602784331445 : ((((((p3 → (p5 → (((False ∧ (p1 ∨ False)) → (False ∨ p3)) ∧ p2))) → p4) ∧ ((True → p1) ∧ (True ∨ (p1 ∨ False)))) ∧ p2) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171665357772395539376821621029 : (((p4 ∧ ((((p2 ∨ ((p1 ∧ p1) ∨ p3)) ∨ True) ∧ p1) ∨ (p5 → False))) ∨ True) ∨ ((p4 ∧ (p3 ∨ ((p4 ∨ p3) → p4))) → (True → p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340947371994014392797792791119 : (p2 → (((p2 ∧ (True ∧ p1)) ∧ ((p4 ∧ p3) → ((False ∧ (p1 ∧ (p2 ∧ ((p4 ∨ True) → (((p4 ∧ p4) → p1) ∧ p3))))) ∨ p1))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316746130037811134118743887086 : (p3 ∨ (True → (((p5 ∨ (False → p2)) → ((p1 → ((p5 ∧ (True ∨ p1)) ∧ p4)) → (p1 ∨ (False ∨ (p4 ∨ True))))) ∨ (p5 → (p2 ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
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
theorem thm_5_vars_40375818063896830542992317619 : ((((((((((p1 ∨ p3) → (((False → p5) → p5) ∧ (p2 ∨ True))) ∧ (True → p3)) ∨ p2) ∨ p1) → p1) ∧ (p1 ∨ True)) ∨ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197560364489626022987287431543 : ((((p5 → (True ∧ p4)) → p1) ∨ (True → p1)) ∨ (((((p4 → (p1 ∧ False)) ∨ True) ∧ (p4 ∨ p4)) ∨ ((p1 ∨ (p1 ∧ False)) → p1)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624979876759323188275980138261 : ((((p5 ∨ (p2 ∨ (p2 → (p3 ∨ ((((True ∨ p3) ∧ p3) → ((p4 ∨ p1) ∨ p5)) ∨ (((p3 ∨ p5) → False) ∧ (p4 ∧ p4))))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606918620572012673012161140018 : ((((((((((p4 ∨ False) ∧ (p1 ∨ ((p2 → True) ∨ (p5 ∨ p5)))) ∧ True) → p1) ∨ False) ∨ (True ∨ (p3 → (p5 ∨ p2)))) ∧ True) ∨ p3) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308359804762087789278884649103 : (p2 ∨ (((False ∨ (((((True → p2) ∧ (p2 ∧ p1)) ∨ (((((p3 ∧ True) → (True ∧ p2)) → True) ∨ p4) ∨ p4)) ∨ p5) ∨ False)) ∧ True) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618803272739250750973398961489 : (((((p2 ∧ (False → p3)) ∧ (((p4 → (False ∧ (((True → ((False → p5) ∧ p4)) → ((p4 ∧ p4) ∨ False)) → True))) ∨ p4) → p3)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117927811000504278685734867574 : ((p5 ∧ ((p1 ∧ True) ∧ ((p3 → ((((p1 ∧ (p3 ∧ False)) ∨ p5) ∧ (p4 ∨ False)) ∧ True)) ∧ (p2 ∨ (p2 ∧ (p3 ∨ p1)))))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_864623562685501645475165836280 : (((((p5 ∨ ((p3 ∧ ((p1 ∨ True) ∨ p4)) ∨ False)) ∨ (p5 → (((p2 → p5) → True) ∧ (((True ∨ p5) ∨ p1) ∨ (True ∨ p5))))) → False) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ ((p3 ∧ ((p1 ∨ True) ∨ p4)) ∨ False)) ∨ (p5 → (((p2 → p5) → True) ∧ (((True ∨ p5) ∨ p1) ∨ (True ∨ p5))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213624962799676011017238770026 : ((((p3 ∧ p3) ∨ p5) ∨ p2) ∨ ((((((((True ∧ p5) → ((p3 ∧ True) ∧ p5)) ∧ p1) ∧ True) ∧ p3) ∧ True) → p4) → ((False ∨ p4) → p4))) := by
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
    apply False.elim h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115396774030509956621019648484 : (((p2 ∧ ((p2 ∧ p1) ∧ ((True ∨ p2) ∧ p2))) ∧ (((True → p3) ∧ (((p5 ∨ False) ∨ ((p4 ∨ p1) → p1)) ∧ False)) ∧ False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249337599209293816435918375443 : ((p4 ∨ p5) ∨ (p5 ∨ ((True ∨ p5) ∧ (p3 → ((p5 ∨ p1) → ((p2 ∨ (((p5 → True) ∨ (True ∨ False)) ∧ (p5 ∨ p4))) ∨ (p1 ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
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
    -- True on the right can always be proven directly.
    apply True.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64571927537058378153916805368 : ((p1 ∨ ((p1 ∨ (p1 ∧ p4)) ∨ (((p5 → ((p3 → p1) → (p3 → False))) → ((p5 ∨ (p2 → p3)) ∧ p1)) ∧ (p3 ∧ (True → p3))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317932759245442270282237958402 : (p4 ∨ ((p1 ∨ (((p3 ∧ p2) → ((p1 → (((((p5 → (False ∨ p5)) ∨ p5) ∧ (p1 → True)) → False) ∧ p2)) ∨ p2)) ∨ (False ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111539942760408359929631895627 : (((((((((p5 ∧ (p1 ∧ p5)) → (p1 ∧ p5)) ∨ p1) ∨ ((p2 ∧ True) ∧ p2)) → ((p3 ∧ p1) ∨ p3)) → False) ∧ p1) ∨ p1) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_698669912824109735345593136737 : (((((True ∧ (p1 → p3)) → ((p3 ∨ p3) → (False ∧ (p3 ∨ p1)))) ∨ ((True ∧ (((False → False) ∨ (False ∧ p2)) ∧ p2)) → (True ∧ True))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330307975447990952078250936658 : (True → (p1 ∨ (((p1 → (p4 ∧ p2)) ∧ ((p4 ∨ ((((p4 ∧ True) ∧ p1) ∧ (((p3 → True) ∧ p3) → False)) ∧ p5)) ∨ p3)) ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_64786149273159641711435388750 : ((p2 ∨ ((((p4 ∨ p4) ∨ (p3 ∧ ((True → ((p2 → p1) ∧ (p3 ∨ p3))) ∨ ((p2 → True) ∨ p1)))) → ((p1 ∧ p2) ∨ p1)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352828417568475659434916135021 : (p4 → ((False → p5) → ((((p5 ∨ (p2 → False)) ∨ ((p4 ∧ ((True → (p2 ∧ (p5 ∧ p4))) ∨ (p3 ∧ p3))) ∧ (p3 → p3))) ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_356266590272066957884290585936 : (p5 → (((p5 ∧ p3) ∨ (((p1 ∨ (p3 ∧ True)) ∧ ((p2 ∨ True) ∧ (p3 ∨ p2))) ∨ p5)) ∨ ((True → p5) → (((False ∧ p1) → True) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68993131644438012109273800184 : ((p5 → (((p5 → ((p2 ∧ ((p5 ∧ (p1 → (p4 ∨ ((p5 → p3) → (p3 ∧ (False ∧ p3)))))) → True)) ∧ (True ∧ False))) → p1) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645323677020269603273578249498 : ((((p4 ∨ (((True ∨ (((p2 ∨ ((p2 → p2) → (False → (True ∨ p2)))) → False) ∧ (p1 → ((p3 → True) → p3)))) ∧ p2) ∨ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54538690043653002067440113288 : ((((p4 ∨ True) → (p1 ∧ ((p5 → False) ∧ p1))) ∨ ((p4 → p1) ∨ (((p1 ∧ p4) ∧ (p3 ∨ p3)) → ((p1 ∧ p3) ∧ (p1 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139510977068173144855820478749 : (((((False → p1) ∧ ((p5 → ((p1 ∨ False) ∨ ((p2 → (p1 ∨ (True ∨ p3))) ∨ p5))) → (True → p2))) → p2) → False) → (p3 ∨ (p5 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((False → p1) ∧ ((p5 → ((p1 ∨ False) ∨ ((p2 → (p1 ∨ (True ∨ p3))) ∨ p5))) → (True → p2))) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → ((p1 ∨ False) ∨ ((p2 → (p1 ∨ (True ∨ p3))) ∨ p5))) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611726447481029524132410281430 : (((((True → (((True → ((p4 ∨ p3) ∨ (p5 ∧ ((p5 → ((p3 ∧ p2) ∨ ((True ∨ p3) ∨ False))) ∧ False)))) ∧ False) → p4)) → p1) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190396672356153743725349068857 : (((p2 ∧ (((p4 → p2) ∨ p1) ∨ (p3 ∧ p3))) ∨ p5) ∨ (((p4 ∨ (((p4 ∨ (p1 ∨ True)) → p3) ∧ True)) ∨ p3) → (p3 → (True ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153213488066622062270435953813 : ((True ∨ ((((p3 ∧ p4) ∨ (p2 → False)) ∧ (True → p5)) ∨ (((p1 ∧ False) ∧ (True ∨ (p2 → p3))) → p4))) → ((p5 ∨ p5) → (p5 ∧ p5))) := by
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
    cases h1
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h12 =>
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h13 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- One of the premise coincides with the conclusion.
          exact h14
        case inr h23 =>
          -- One of the premise coincides with the conclusion.
          exact h14
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h28.left
        let h30 := h28.right
        -- Disjunctions on the left can always be decomposed.
        cases h29
        case inl h31 =>
          -- Conjunctions on the left can always be decomposed.
          let h32 := h31.left
          let h33 := h31.right
          -- One of the premise coincides with the conclusion.
          exact h25
        case inr h34 =>
          -- One of the premise coincides with the conclusion.
          exact h25
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h25
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h37 =>
      -- One of the premise coincides with the conclusion.
      exact h36
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- Conjunctions on the left can always be decomposed.
        let h40 := h39.left
        let h41 := h39.right
        -- Disjunctions on the left can always be decomposed.
        cases h40
        case inl h42 =>
          -- Conjunctions on the left can always be decomposed.
          let h43 := h42.left
          let h44 := h42.right
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h45 =>
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h46 =>
        -- One of the premise coincides with the conclusion.
        exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731817232772416186092742223423 : ((((p4 → (False ∧ p4)) → (p1 ∧ (p3 ∨ (p5 → (((True ∨ p3) → False) ∨ (p1 ∨ ((p1 ∨ (p5 ∨ (p5 → p4))) ∧ (p5 → p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52680356265134090501819105905 : (((p3 ∨ (((p2 → (p4 → (False ∨ p5))) ∨ (False ∧ False)) ∧ (True → p1))) ∨ (((((p2 ∧ (p4 → p2)) → p2) ∨ p3) ∨ p2) ∨ p2)) ∨ False) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323745181533028986481449236160 : (p5 ∨ ((((True ∨ (True ∨ p2)) → ((((False ∨ p4) ∨ False) ∧ ((p2 ∧ p2) ∧ True)) ∨ True)) ∨ False) ∧ ((((True ∧ False) ∧ False) ∧ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255059286773229264160774362755 : ((p4 ∧ p2) → (((p5 → (((p4 ∨ (p1 ∨ ((((p2 ∧ p3) ∧ True) → p4) ∧ p3))) → False) → (p4 → (p2 ∨ (p2 ∧ p2))))) → False) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336449999751273465865282815879 : (p1 → ((p5 ∨ (p3 ∧ ((p2 ∨ ((((p4 ∨ True) ∨ False) ∨ p2) ∧ (p2 ∨ p5))) ∧ (((p1 ∧ True) ∨ (p2 ∧ (True → p2))) ∧ p2)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734912173615952746928785788034 : ((((p2 ∨ p3) ∧ (p3 ∨ (p2 ∨ ((((p5 ∨ p1) → ((False → ((False ∨ p2) ∧ (p4 ∨ ((False ∧ p1) ∨ False)))) ∧ p2)) → False) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114666837750966627770192519749 : ((((True → p3) ∧ (False ∨ (p2 ∧ (((p4 → p2) ∨ p2) → (True → (p3 ∧ True)))))) ∨ (p2 ∧ (False ∧ ((False → p2) → p2)))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137542976626048933175469329311 : ((p5 ∧ (p5 → (((p5 → (((p3 ∧ True) ∨ False) ∨ ((p5 → (((False ∨ p4) ∧ True) ∨ p1)) → False))) ∨ p1) ∨ p5))) ∨ ((False ∧ p2) → p4)) := by
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
theorem thm_5_vars_317780825533360992881488347875 : (p4 ∨ ((((((p5 → p2) → p2) ∧ ((False ∨ p3) ∨ p5)) ∧ (True ∧ True)) ∨ (((p4 → ((p1 → (True → False)) ∨ False)) ∨ p5) → p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304991004055529082433032860483 : (p1 ∨ ((((True ∧ (p5 ∧ p1)) ∨ (((p1 → (False → (True → ((p2 → p5) ∧ p3)))) → (p1 ∧ True)) → p4)) → p4) ∨ (False → (False ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_139207735292187780067931478212 : (((((p2 → p4) ∨ p4) ∧ (p4 ∨ (p4 ∧ (((((p1 ∧ p4) ∨ p5) ∧ (p3 ∧ p4)) ∨ p4) ∨ (p3 ∧ True))))) ∨ p1) → ((True → p3) → p3)) := by
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
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h8 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h9 := h2 h8
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h13
          case inl h14 =>
            -- Conjunctions on the left can always be decomposed.
            let h15 := h14.left
            let h16 := h14.right
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h17 =>
              -- Conjunctions on the left can always be decomposed.
              let h18 := h17.left
              let h19 := h17.right
              -- Conjunctions on the left can always be decomposed.
              let h20 := h16.left
              let h21 := h16.right
              -- One of the premise coincides with the conclusion.
              exact h20
            case inr h22 =>
              -- Conjunctions on the left can always be decomposed.
              let h23 := h16.left
              let h24 := h16.right
              -- One of the premise coincides with the conclusion.
              exact h23
          case inr h25 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h26 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h27 := h2 h26
            -- One of the premise coincides with the conclusion.
            exact h27
        case inr h28 =>
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- One of the premise coincides with the conclusion.
          exact h29
    case inr h31 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h32 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h33 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h34 := h2 h33
        -- One of the premise coincides with the conclusion.
        exact h34
      case inr h35 =>
        -- Conjunctions on the left can always be decomposed.
        let h36 := h35.left
        let h37 := h35.right
        -- Disjunctions on the left can always be decomposed.
        cases h37
        case inl h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Conjunctions on the left can always be decomposed.
            let h40 := h39.left
            let h41 := h39.right
            -- Disjunctions on the left can always be decomposed.
            cases h40
            case inl h42 =>
              -- Conjunctions on the left can always be decomposed.
              let h43 := h42.left
              let h44 := h42.right
              -- Conjunctions on the left can always be decomposed.
              let h45 := h41.left
              let h46 := h41.right
              -- One of the premise coincides with the conclusion.
              exact h45
            case inr h47 =>
              -- Conjunctions on the left can always be decomposed.
              let h48 := h41.left
              let h49 := h41.right
              -- One of the premise coincides with the conclusion.
              exact h48
          case inr h50 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h51 : True := by
              -- True on the right can always be proven directly.
              apply True.intro
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h52 := h2 h51
            -- One of the premise coincides with the conclusion.
            exact h52
        case inr h53 =>
          -- Conjunctions on the left can always be decomposed.
          let h54 := h53.left
          let h55 := h53.right
          -- One of the premise coincides with the conclusion.
          exact h54
  case inr h56 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h57 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h58 := h2 h57
    -- One of the premise coincides with the conclusion.
    exact h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190641519477849138553848339752 : (((False ∨ ((True ∧ ((p4 → p3) ∨ True)) → True)) → p3) ∨ (((True → p3) ∧ p1) → (p5 ∨ ((p4 → (p4 ∨ p5)) → ((p4 → p5) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54844631012471868388319201920 : (((p5 → (True ∨ ((False → True) ∧ (True ∨ p1)))) → (((((p2 ∧ (True ∧ p3)) ∨ ((True → (p1 ∨ p1)) → p1)) → p4) ∧ p3) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_785993209944417462756572207901 : (((p4 ∨ ((False ∧ ((p4 ∨ (True → p5)) ∧ ((p4 → p4) ∧ ((p5 → False) ∧ (False ∨ ((p5 ∨ (False → p1)) → p4)))))) ∨ (p3 → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158062495334075267892086178522 : (((p3 → ((p1 ∨ (p1 ∧ True)) ∨ p2)) ∨ ((((p1 → (p1 → p2)) ∧ (p2 → p3)) ∨ p3) ∧ True)) ∨ ((True ∧ False) → ((p2 ∧ p2) → p4))) := by
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
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112263107153798516225508438109 : (((p5 ∨ (((((p3 ∨ False) ∧ p2) ∨ ((p4 → ((p1 → p4) ∨ ((False ∧ (p5 ∧ p4)) ∧ p1))) ∨ True)) ∨ p3) → p2)) ∨ p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344651231675771326455256798292 : (p2 → (p2 → ((((p5 ∧ (True → ((p3 ∧ (True ∨ ((p5 ∨ p3) ∧ p4))) ∧ (p3 ∧ p2)))) ∨ (p4 ∨ p1)) ∧ (p3 → (True → p4))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674239491775527551279094377899 : ((((p5 ∧ (p4 ∨ ((p2 → ((p3 ∨ p2) ∨ (p5 ∨ ((p1 ∨ (True ∧ ((p3 → p2) ∨ p1))) ∧ p4)))) → p1))) → (p2 → (p4 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351252513274442919929028654681 : (p4 → (((p4 → True) → (p2 ∧ (p2 ∧ (p2 ∧ ((p1 → p4) → ((((p5 → (True → False)) ∨ False) ∧ p2) ∨ p3)))))) ∨ (p5 → (p3 ∨ True)))) := by
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
theorem thm_5_vars_32232691343343049552652521051 : ((p1 ∨ ((p4 ∧ p5) ∨ (((p2 → ((((p3 ∧ p3) → ((p2 → (True ∨ False)) ∨ True)) ∧ False) ∧ (True ∧ p5))) ∨ (False → True)) ∨ p2))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61968264342177855689372486218 : ((p2 ∧ ((((((p5 ∧ (p1 → p2)) ∨ p3) → p2) → p5) ∨ False) ∧ ((p1 → False) ∧ (p5 → ((False ∧ ((False ∧ p2) → p5)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151059736701033093612018491769 : ((((((p1 → False) ∧ ((True → (p4 ∧ True)) ∧ (p2 ∧ ((p4 → (p2 ∧ p3)) → False)))) ∧ p2) ∨ True) → p1) → (((p2 ∨ p2) ∨ p4) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 → False) ∧ ((True → (p4 ∧ True)) ∧ (p2 ∧ ((p4 → (p2 ∧ p3)) → False)))) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_645336089656568840126559934846 : ((((p4 ∨ ((((p2 ∧ (p2 → p1)) → p4) ∧ (p5 → (((p4 → False) ∨ (False ∨ p5)) ∧ (False ∧ ((False → p3) → p3))))) ∨ p4)) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67767471220134714244177615807 : ((p2 → ((((p2 → p3) ∧ (p2 ∨ (p3 ∧ p1))) ∧ ((True ∨ (p2 ∨ (False → ((p5 → (p1 ∨ False)) ∨ p1)))) → (True ∧ p5))) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161505432268921741016691806445 : ((p4 ∧ (((p5 ∧ p5) ∧ (p5 ∨ (p2 ∨ (False ∧ p1)))) ∧ (p4 ∨ ((p5 ∧ p5) → (False → False))))) → ((p5 ∧ ((True ∧ p3) ∨ p3)) ∨ p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152599356489605881657734858793 : (((p2 ∧ p4) ∧ ((((p2 ∧ (True ∧ (p5 → (False ∨ p1)))) → ((False ∧ True) ∨ (p1 → p3))) ∧ p1) ∧ True)) → (((True → p5) ∨ False) ∨ True)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758722555687801258960572328071 : (((p2 ∧ (((False → True) → (p3 → (((p3 ∧ p2) ∧ (p5 ∧ (((True → (p1 → (p3 ∨ (p2 → p1)))) → p4) ∨ p1))) ∧ p1))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262178387750502692844546610320 : (True ∧ ((((p4 ∧ (True → ((True ∧ (True ∨ (p3 → (p2 → ((True ∧ (p2 ∧ p3)) → (p5 ∨ (p1 ∧ p4))))))) ∨ True))) ∧ p5) → False) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727157263883522989907674971351 : ((((True ∧ (True → p1)) ∨ ((True → p4) ∧ ((p5 → p4) → (False ∧ (((p2 → False) → (False ∧ ((p4 → p5) ∧ p2))) ∧ (p3 ∨ p2)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48431407140142399196774249082 : (((p4 → (((p2 ∨ ((True → (True → ((p5 ∧ False) ∧ True))) ∧ (p5 ∨ p4))) → (((p3 ∧ False) ∨ p4) ∨ p4)) ∧ p1)) → (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137847363763947598517249148914 : ((p3 ∨ (((p1 ∨ p2) ∧ p4) ∧ (((p1 ∨ (((p1 ∧ p2) ∨ True) ∧ p2)) ∨ p1) ∨ ((True ∧ False) ∨ (p2 → p5))))) ∨ (p5 → (p4 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701487099140969744038235186037 : ((((((p1 ∨ p1) → p3) ∨ (True → (p3 ∨ (p3 ∨ p5)))) ∧ ((((p3 → p5) → (((p4 → p2) ∧ (p4 ∨ True)) ∧ p1)) ∨ p5) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123951773713838020414115140900 : (((p3 ∨ ((p3 ∨ (False ∨ ((True → p4) → (p5 ∧ False)))) → p2)) ∧ ((False ∧ (p1 ∨ ((p4 ∨ False) ∧ (False ∧ p3)))) ∨ p5)) → (p4 → p4)) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168137181025959225174103774620 : (((p2 ∧ ((False ∨ p4) ∨ p2)) → ((p3 ∧ ((False ∧ (p3 → p1)) → False)) ∨ (p1 → p5))) → ((p1 ∧ p4) → ((p3 ∧ (False → p5)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193442883376646239133264658004 : (((p2 → True) ∧ (((p5 ∨ p4) → False) ∨ (p5 → True))) → (p1 → ((p3 → False) ∨ (True ∨ ((p4 ∨ ((p4 ∧ (p4 → p2)) ∨ True)) ∧ p1))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196746097416677910698823477270 : ((((p4 ∧ (False ∧ p2)) ∧ (False ∧ p1)) ∧ p2) ∨ ((((p3 ∧ (p1 ∧ ((p5 → (True → p4)) → True))) ∨ ((False → p4) ∨ p4)) ∨ p1) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943228373208663811370658173904 : (((((True → True) → (p4 ∧ False)) ∧ ((((p2 ∧ p1) ∨ p3) ∨ p2) ∨ (p1 → ((p1 ∧ p5) ∧ (p3 → (True ∧ (p5 → (True ∧ p5)))))))) → p4) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h9 : (True → True) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h11 := h2 h9
        -- We need to get the left conjuct of h11 based on <expert-advice>.
        let h12 := h11.left
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h14 : (True → True) := by
          -- Implications on the right can always be decomposed.
          intro h15
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h14
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : (True → True) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h19
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- One of the premise coincides with the conclusion.
      exact h22
  case inr h23 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h24 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h25
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h26 := h2 h24
    -- We need to get the left conjuct of h26 based on <expert-advice>.
    let h27 := h26.left
    -- One of the premise coincides with the conclusion.
    exact h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44082293517257310310818363289 : (((((p4 → (p5 → p5)) ∨ ((((p1 ∧ False) ∨ p1) ∧ p4) → (p5 ∧ (p5 → (p4 ∨ (True ∨ True)))))) ∧ (p4 ∨ (p5 ∧ p1))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693779613362481917047643799632 : ((((((p3 ∧ (p5 → (p5 → (True → ((p1 → p5) → p2))))) ∨ p1) → p4) ∨ (((p2 → ((p1 ∨ p3) → (p5 ∧ p4))) ∨ p1) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_193873600521467778538188832546 : ((False ∨ (((p2 ∨ (True → False)) → (p5 → True)) ∨ p2)) → ((p3 ∧ (((True ∧ (((p3 → p2) ∧ False) ∨ True)) → (False ∧ False)) ∨ False)) → p2)) := by
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
    cases h1
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h9 : (True ∧ (((p3 → p2) ∧ False) ∨ True)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h10 := h5 h9
        -- We need to get the left conjuct of h10 based on <expert-advice>.
        let h11 := h10.left
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175470221824520701878967162722 : ((p2 → ((True ∨ ((False ∨ p5) ∨ (True ∧ (True ∧ p4)))) → ((p5 ∨ p1) ∨ False))) → ((True → p2) ∨ ((True ∨ (True ∧ p5)) ∨ (p4 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85170398322823679098727527091 : (((((p3 ∨ (False ∧ p1)) ∨ (p4 ∨ False)) ∨ (((p3 ∧ p5) → True) ∨ False)) → ((p4 → (((False → p5) → p3) → False)) ∧ (True ∧ p1))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ (False ∧ p1)) ∨ (p4 ∨ False)) ∨ (((p3 ∧ p5) → True) ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658404793464745724115246541909 : ((((False ∨ (p3 ∧ ((p1 ∧ (p1 → ((p2 → False) ∨ (((False ∨ (False ∨ p4)) → p4) → ((True → p2) ∨ p5))))) ∧ p3))) ∨ (False → p4)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219340894921635108564070536293 : ((p2 ∨ (False → (True ∨ p1))) → (p2 ∨ ((False → ((p3 ∨ (False ∨ True)) ∧ (p5 → p2))) → ((False ∨ (p1 → p4)) ∨ ((p1 ∧ False) → p3))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254888613942397891179246813698 : ((p4 ∧ True) → (((p4 ∧ (p2 ∨ (((False ∧ ((True → False) ∨ ((p1 ∧ (p3 ∧ (p4 ∧ True))) ∧ p4))) ∨ p3) ∧ p5))) ∨ p4) ∨ (p2 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44275767861398137998757030277 : ((((p3 ∨ (p2 ∧ (((p3 ∨ p4) ∨ True) → ((False ∧ (p1 ∧ ((p3 ∧ p4) ∨ p3))) ∧ p5)))) → (p2 ∧ (p5 → (p5 → p2)))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677790032924433377772268530533 : (((((p3 → (((False ∧ p5) → (False ∧ ((p5 → (p3 ∧ p5)) ∧ ((False ∨ False) ∧ p5)))) ∨ p5)) → False) ∨ ((p1 → p2) ∨ (p2 → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118758646870673036183842132089 : ((p5 ∨ ((p1 ∨ p3) ∨ ((p3 ∧ ((True ∨ (False ∨ p4)) → (p1 ∧ (p5 ∧ ((p1 ∧ p3) ∧ True))))) → ((True ∨ p3) → p5)))) ∨ (p4 ∧ p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (True ∨ (False ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
    have h13 : (True ∨ (False ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h12, we can now drive its conclusion.
    let h14 := h12 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the left conjuct of h15 based on <expert-advice>.
    let h16 := h15.left
    -- One of the premise coincides with the conclusion.
    exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305886623903567699281638325422 : (p1 ∨ ((p4 ∧ (((p3 → True) ∨ p3) → False)) ∨ (True ∨ ((False ∧ (p2 → p4)) ∨ ((((p2 → False) ∧ (p5 → p4)) ∧ p3) → (p2 ∧ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_716893840040700804568192016750 : ((((p2 ∧ ((p2 → p2) ∨ p5)) ∧ (p2 ∨ ((p4 → ((p3 → (p1 ∧ ((p2 ∨ (p2 ∨ (p5 ∧ False))) ∧ p5))) → False)) → (p1 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89360279459546412769767793694 : (((True → (p2 ∧ False)) ∧ (((p4 ∨ p3) ∧ True) ∨ (p3 ∨ ((True ∧ ((p5 ∧ (False → p2)) → p3)) ∨ ((p3 ∨ p4) ∧ (True → p4)))))) → p5) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the right conjuct of h18 based on <expert-advice>.
      let h19 := h18.right
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h24 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h25 := h2 h24
        -- We need to get the right conjuct of h25 based on <expert-advice>.
        let h26 := h25.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h30 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h31 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h32 := h2 h31
          -- We need to get the right conjuct of h32 based on <expert-advice>.
          let h33 := h32.right
          -- False on the left can always be used.
          apply False.elim h33
        case inr h34 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h35 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h36 := h2 h35
          -- We need to get the right conjuct of h36 based on <expert-advice>.
          let h37 := h36.right
          -- False on the left can always be used.
          apply False.elim h37



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58224535018931003634645874406 : (((p4 ∧ p3) ∧ (p5 ∨ (((((p4 ∧ (((False ∧ False) ∧ p5) → p4)) ∨ (p5 → (p3 → False))) ∧ p5) ∧ (p4 ∨ (p2 ∧ p2))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58519075162911676432220757117 : (((p5 ∨ False) ∧ ((p3 → (((False → (((p2 → p5) ∧ (False ∨ p1)) ∧ ((p5 → True) ∧ p5))) ∧ ((False ∨ p2) ∨ p2)) → p1)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214487145570417071393321975752 : (((p1 ∧ p4) ∧ (p4 ∨ True)) ∨ ((True → False) → (((False → (True → (((p1 ∨ p3) ∧ (p4 ∨ p3)) ∨ p5))) ∨ (p5 ∨ (False ∨ p5))) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h8 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h9 := h1 h8
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h14 := h1 h13
        -- False on the left can always be used.
        apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49260928465621595770184950543 : (((p1 ∧ ((p3 ∨ ((False ∨ p3) ∧ ((p4 → p4) ∧ ((p5 → p1) ∧ ((True ∧ p4) → (p5 ∧ False)))))) ∧ p4)) ∨ ((p5 ∧ p5) → p5)) ∨ p2) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725132908729490326740661488705 : ((((p1 → (p1 ∨ p1)) ∧ ((True ∧ ((p3 → (((True ∨ (p5 → p5)) ∧ p1) ∧ False)) ∨ p3)) ∧ (False ∨ ((p4 ∧ (p3 → p4)) ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



