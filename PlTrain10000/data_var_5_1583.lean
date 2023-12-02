variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227589047219542513029277797585 : ((False ∧ (p2 ∧ p3)) ∨ (((p4 ∧ p5) ∧ (p4 → (p3 ∨ (p2 ∧ p3)))) → (p1 → ((((False ∨ ((True → False) → p5)) → p3) ∨ p1) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612528298058851913080280548484 : (((((((False → p2) → (p1 ∧ (p2 ∨ (((((True ∨ True) ∧ (p2 ∧ True)) ∧ (p4 ∧ p4)) ∧ p3) ∧ p1)))) ∨ True) ∨ (p4 ∨ p5)) ∨ p2) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722967514073588996074761099075 : (((((True ∨ True) ∨ p5) ∧ (((((p2 → p3) ∧ (p4 → True)) → False) ∨ True) ∨ (p2 → ((((False → p2) → p5) → p1) ∧ (p2 ∧ p2))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_324195529851983102329048250732 : (p5 ∨ (((True ∨ (p2 ∧ (p5 ∨ ((p1 ∧ p2) → True)))) → p5) → ((p3 → ((p5 ∧ False) ∧ p5)) ∨ ((p5 ∨ (p3 → (p2 → p1))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p2 ∧ (p5 ∨ ((p1 ∧ p2) → True)))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152466293700423319176016067450 : (((True → (p3 ∨ True)) ∧ ((((False ∨ True) ∨ True) ∨ (p5 ∨ p1)) ∨ ((p1 ∧ (p3 ∧ (p5 ∨ False))) → p5))) → (((True ∧ False) ∨ p2) ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_732716876232561753066939627866 : ((((p1 ∧ p4) ∧ (((((p1 ∨ (((False ∧ p2) → (p4 ∨ (True → p5))) → p5)) ∨ p3) ∧ (p1 ∧ ((False → p1) → p5))) ∨ p4) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257322145367968228738784995672 : ((p2 ∨ p4) → (((True ∨ p5) ∧ ((((p2 ∨ (p2 → p1)) ∧ (p3 ∧ p2)) ∧ (p3 ∧ ((p2 ∧ p5) → p5))) ∧ p3)) ∨ ((False → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180863128153919965728408207037 : (((p5 ∧ (p2 → p1)) ∨ ((True → p5) ∨ (p3 ∧ (p1 ∨ (p2 ∨ p1))))) → ((((p4 ∧ p5) ∧ p2) → ((False ∨ p1) ∨ p2)) ∨ (False ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Conjunctions on the left can always be decomposed.
        let h24 := h22.left
        let h25 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h28
          -- Conjunctions on the left can always be decomposed.
          let h29 := h28.left
          let h30 := h28.right
          -- Conjunctions on the left can always be decomposed.
          let h31 := h29.left
          let h32 := h29.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h30
        case inr h33 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h34
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- Conjunctions on the left can always be decomposed.
          let h37 := h35.left
          let h38 := h35.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114669063227010634014142075536 : ((((True → p3) ∨ ((False → True) → (p2 ∧ ((((p5 ∧ True) → p5) ∧ p2) ∧ p2)))) ∨ (((p2 → p3) → p3) ∨ (p5 ∨ True))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114915703800423153557125296437 : ((((True ∨ (p1 ∨ (True ∨ (p2 ∨ ((True ∨ (p5 ∧ p1)) ∨ False))))) ∨ p1) → ((p3 → p3) → (False ∨ (p4 ∧ (p5 → p2))))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478515935473096962933505454469 : ((((p3 → ((p3 ∧ ((p1 ∧ p2) ∨ (True ∨ True))) ∧ p3)) → (((True → p5) → (((False → p1) ∧ (p4 ∨ (True → p4))) ∨ p3)) ∨ True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161719337300076602387250084350 : ((p3 ∨ (((((p4 ∧ False) ∧ ((((p3 ∨ False) → p5) ∨ p4) ∧ (p3 → p2))) ∨ p2) ∧ p3) → False)) → (True → ((p3 ∨ False) ∨ (p2 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
theorem thm_5_vars_799279514589949498306023498228 : (((p1 → (p3 ∧ (p2 → (((p2 ∧ p5) ∧ (((p3 ∧ (p3 → p1)) → ((((p3 ∧ p3) → p1) → p5) ∧ True)) ∨ True)) ∨ (p1 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218149834300371289837112346020 : (((p5 → True) ∧ (p3 → p1)) → (((((False ∨ p1) ∨ ((p3 ∨ p1) ∧ p3)) ∧ (p2 ∧ (p4 ∧ ((p4 → (p1 ∨ p3)) ∧ p2)))) ∨ True) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_929838585212746145438751665465 : ((((p5 ∧ (((p1 ∨ ((True → p3) ∧ p2)) → p1) ∨ True)) ∨ (((p3 → (p4 ∨ ((p5 ∧ False) → (False ∧ p2)))) → False) ∧ (p3 ∨ p1))) → p5) ∧ True) := by
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
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h11 : (p3 → (p4 ∨ ((p5 ∧ False) → (False ∧ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h13
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- False on the left can always be used.
        apply False.elim h15
        -- Conjunctions on the left can always be decomposed.
        let h16 := h13.left
        let h17 := h13.right
        -- False on the left can always be used.
        apply False.elim h17
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h18 := h8 h11
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h20 : (p3 → (p4 ∨ ((p5 ∧ False) → (False ∧ p2)))) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- False on the left can always be used.
        apply False.elim h24
        -- Conjunctions on the left can always be decomposed.
        let h25 := h22.left
        let h26 := h22.right
        -- False on the left can always be used.
        apply False.elim h26
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h27 := h8 h20
      -- False on the left can always be used.
      apply False.elim h27
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112917001702334497369841712730 : ((((False → p4) ∨ ((False ∧ True) ∨ (False → ((True ∧ (p3 ∨ (False ∧ True))) ∨ ((((p2 ∧ p3) ∧ p1) ∨ p1) → False))))) → False) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319633420425142570547937360784 : (p4 ∨ ((((((False ∨ p5) → p1) → True) ∧ p3) → p1) ∨ (((p2 ∧ ((p2 ∧ p2) ∨ (p3 → (True ∨ False)))) ∧ (p1 ∧ (p3 ∨ p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350544583402324908079520960666 : (p4 → (((((p3 → (True ∧ True)) → ((True ∨ p3) → p5)) ∨ (((p5 ∨ p2) ∧ p1) ∨ p2)) ∧ (((p1 ∨ True) ∨ p2) → (p3 ∧ False))) → p1)) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∨ True) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h15 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h16 : ((p1 ∨ True) ∨ p2) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h17 := h4 h16
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- False on the left can always be used.
      apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791418322593574270901866111811 : (((True → ((((p3 ∨ (p2 ∨ False)) ∨ p2) ∨ (((p2 ∧ ((p1 ∨ p1) ∧ (((False ∧ p5) ∨ p2) ∨ (False → p2)))) → p4) ∨ p3)) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671545956196583728176486116064 : ((((p4 → (((p2 ∨ (p5 ∧ (p3 ∨ (True ∨ (False ∨ (False ∧ p2)))))) ∨ p2) ∧ (((p5 → True) ∨ False) ∧ p5))) ∨ ((p5 ∧ p5) → p5)) ∨ p1) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231364282298892942758657745926 : (((False → p2) ∨ True) → ((p3 ∨ ((p5 → (((p4 → p2) → p2) → (p1 → ((((p2 ∨ (False ∧ p1)) ∧ False) ∧ p2) ∨ p5)))) ∨ p2)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232156519220325456796608810618 : (((True → p2) → p5) → (((p5 ∨ p5) ∧ (((True ∨ (p3 ∨ (p4 → False))) ∨ ((p1 ∧ (p1 → p5)) → p2)) ∨ p3)) → (p5 → (p2 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h9
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h11 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h12 =>
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h13 =>
            -- One of the premise coincides with the conclusion.
            exact h7
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h20 =>
          -- Disjunctions on the left can always be decomposed.
          cases h20
          case inl h21 =>
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h22 =>
            -- One of the premise coincides with the conclusion.
            exact h16
      case inr h23 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h24 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242160977692619130006721714839 : ((p2 → True) ∧ (True ∧ ((((p2 ∨ p3) ∧ (p3 → p1)) → p5) → ((False ∨ ((False ∨ p5) ∧ p1)) ∨ (True ∨ (p5 → ((p1 ∧ False) ∨ p4))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697168317183862481817293871878 : ((((((p5 → p5) ∨ p4) ∧ (False ∨ ((p3 ∨ (p3 ∧ False)) ∧ False))) ∧ ((False → ((p4 → (p2 ∧ p2)) ∨ p5)) ∨ ((p1 ∨ p1) ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58366325317724265089837160138 : (((p1 ∨ p1) ∧ (((((p3 ∨ ((((p4 ∧ (((p3 ∨ p5) ∨ (p4 → p3)) ∧ p5)) ∨ p2) → False) ∨ p4)) ∨ False) ∨ p1) → p2) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40130121221999914004529474102 : ((((((p3 → (((p5 ∨ (p5 → p2)) → (False ∧ (((p4 ∨ p4) → p5) ∧ p5))) → p3)) → p5) → ((p4 ∨ p1) → p3)) ∧ p1) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124962941259400909542622390030 : (((p1 ∨ ((False → p3) ∨ p4)) → ((((((True ∧ False) → p4) ∧ ((True ∧ p4) ∨ (p3 ∧ p4))) → p3) ∨ p3) ∧ (p2 ∧ p5))) → (p2 ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ ((False → p3) ∨ p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172213304419014125934194834004 : ((((p2 ∨ False) ∨ (p3 ∨ (p2 → (True ∨ (p1 ∨ True))))) → ((p4 ∨ p4) → False)) ∨ ((p2 → (True → False)) → (((p3 → p3) ∨ p3) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256641494954662551555381580853 : ((p1 ∨ False) → ((p2 ∨ (((((((p3 ∨ (False ∨ p4)) ∧ (False → p3)) → (p4 → (p4 ∧ (p4 ∨ False)))) ∧ p4) → p3) → p5) ∨ True)) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_637699736590560089036470282557 : ((((((True → (((p2 → p2) ∧ (False ∧ True)) ∧ True)) → p1) → (((True ∨ ((p3 ∧ p1) → False)) ∨ True) ∧ ((p5 → p2) ∨ True))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69097247629949297297431366992 : ((p5 → ((False → (((p1 → (p4 → (((p3 ∧ True) ∨ p2) ∧ (((p4 ∧ True) ∨ (True → p1)) ∧ True)))) → p5) ∨ (p2 ∨ p1))) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53145922026203537378156188161 : ((((((False → (p4 ∧ (p3 ∧ (True ∨ p2)))) → False) ∧ p2) ∨ True) ∨ (p3 → ((((p5 ∨ (p2 ∨ p5)) ∨ p4) → False) → (p2 ∧ p5)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55578674326391058016366032711 : (((p1 ∨ ((False → (p3 ∧ p2)) → p1)) → ((((p3 ∧ p2) ∨ False) ∨ ((p4 → ((p1 ∨ (False ∧ p1)) ∧ p1)) ∨ p5)) ∨ (p4 ∨ p4))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (False → (p3 ∧ p2)) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h6
      -- False on the left can always be used.
      apply False.elim h6
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118455128771114555958609018439 : ((p3 ∨ (((p4 ∧ (((p3 → (True ∧ (((p5 ∧ ((p4 ∧ False) → p4)) → p1) ∧ (False ∧ True)))) ∨ False) ∨ p4)) ∨ False) ∨ True)) ∨ (False ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674333618467205019889898633063 : ((((p1 ∨ ((((p1 ∧ p2) → (((p3 ∨ (False ∧ (p3 → p3))) ∧ p3) ∧ False)) → (p4 ∨ (p4 → False))) ∧ p3)) → ((p1 → p5) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715520972823057250616957807386 : ((((((p2 → p4) → p3) ∧ p3) ∧ ((p2 → (((((((p2 ∨ p3) ∨ False) → p5) → (True → False)) → True) → p5) ∨ p5)) ∨ (p1 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58654559329199774223487629173 : (((p1 → p3) ∧ ((p2 ∧ (p5 ∨ ((p1 → ((p2 ∨ False) ∨ p5)) ∨ (False → ((True ∧ (p3 ∧ p5)) ∨ False))))) ∧ ((p4 ∧ p4) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160890354656700941424457857384 : ((((True → p1) ∨ (p1 → p5)) ∨ ((((p4 ∨ p3) → p1) → (((p5 ∨ True) ∨ p1) ∧ p1)) ∧ True)) → ((p1 → True) → ((True ∧ p1) ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2069543365931375851273105709 : ((((p3 ∨ p1) → (((False ∨ ((p3 → p2) ∧ p3)) → True) → (p5 ∨ (p5 ∨ p4)))) ∧ p5) ∨ ((False ∧ ((p1 ∨ p5) ∧ p3)) → p2)) := by
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
theorem thm_5_vars_113869429455216932748508863270 : (((p5 → (True ∨ (p5 ∨ ((((p2 ∨ (p2 ∧ p2)) ∧ (True ∧ True)) ∧ ((p2 ∧ (p3 → False)) ∧ p1)) → True)))) → (p2 ∧ p2)) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659222674616232062032339537426 : ((((p4 → (((False ∧ p4) ∨ (p5 ∧ (((p4 ∧ p2) ∧ ((p1 ∨ p2) ∧ p1)) ∨ (p3 ∨ p1)))) ∧ (True ∨ (p5 → p4)))) ∨ (False → p1)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_140944239612594015368195017390 : ((((((p2 ∧ False) ∨ p4) ∨ (p4 ∧ p5)) ∨ (p4 ∨ p2)) ∨ ((p3 ∧ (p3 ∧ (True ∨ ((p5 → False) → p4)))) ∧ p5)) → ((False ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h5 =>
          -- Conjunctions on the left can always be decomposed.
          let h6 := h5.left
          let h7 := h5.right
          -- False on the left can always be used.
          apply False.elim h7
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h18 := h16.left
    let h19 := h16.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190924439456811700396652090042 : (((((p4 ∧ p3) → p5) ∨ False) ∧ (p2 → (p1 ∧ p5))) ∨ ((((p3 ∧ (p1 → (p1 ∨ p5))) ∧ (p5 → p3)) ∧ (p2 ∧ False)) ∨ (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54897466386595786519008826005 : ((((p2 ∧ (p5 ∧ (p3 ∨ True))) ∨ True) ∧ ((p3 ∧ p5) ∧ (((p3 ∧ (p4 → (True → p4))) → ((p5 → p1) ∨ (p2 ∨ p3))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114391399379971866631245856715 : ((((((True ∧ (p5 ∨ False)) ∧ ((True ∧ p3) ∧ False)) ∧ (p5 ∧ p5)) ∧ (p2 → (p5 ∨ False))) ∨ ((True ∨ p4) ∧ (p4 → p3))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42338923516536080896936528327 : (((p3 ∧ ((p5 ∨ ((p3 ∨ (p2 → ((p4 ∧ p2) ∨ (p5 → ((False ∧ ((p4 → p2) ∨ False)) → p3))))) → (p2 → p5))) → p4)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349094544550704305179203984957 : (p3 → (True → ((p5 ∧ (((p2 ∧ True) ∧ (((((p3 → p2) ∧ p5) ∧ (True → p1)) → ((True → p4) ∧ p3)) → (False ∧ p4))) ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259887976800515759079749282363 : ((p1 → p4) → ((p5 → (p4 ∨ p3)) ∨ (p1 → ((((p3 ∧ (((True → p4) → p5) ∨ (False ∧ True))) ∧ p3) ∨ ((True → p5) ∨ p5)) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338870821116423297682287283055 : (p1 → ((True ∧ True) → (p5 → ((p1 → (False ∨ ((p2 → p1) → (False ∨ p3)))) → ((p4 ∧ ((False ∨ (True → False)) ∧ p3)) ∨ (True → p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43458021177359122511529818270 : (((((p2 ∧ p2) ∨ ((((p2 ∨ (p3 ∨ p5)) ∨ p3) → (p3 ∨ (p4 ∨ p3))) ∧ ((p5 ∨ p5) → ((p4 ∧ p4) ∨ p5)))) ∨ p4) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232408415485072076764527191518 : (((p5 → p5) → p3) → (p4 → (((((p5 ∨ (((p4 ∨ True) ∧ p1) ∨ (False → (False ∨ p4)))) → p1) ∧ ((False ∧ p4) ∧ p1)) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_793648788128253561536626206711 : (((True → (p5 ∨ (((False ∨ (((((p3 ∧ False) → (True ∨ (p4 → p1))) ∧ ((p4 → p2) ∧ False)) ∨ True) ∧ (p4 ∨ p5))) ∧ False) ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134547534644905709176931279496 : ((((((p4 → (False ∧ False)) → p3) ∨ (p2 ∧ (((((False ∨ p2) → p5) ∧ (p1 ∨ p3)) → p5) ∨ True))) → p4) → p5) ∨ ((False ∧ p2) → p3)) := by
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
theorem thm_5_vars_187061656746159385397187547983 : (((p1 ∨ True) ∧ ((((p5 → False) → p1) → True) → (p1 → p5))) → (((p5 → (((p1 ∧ (True ∧ p4)) ∨ p2) ∧ True)) ∨ False) ∨ (p2 → p2))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198253947403536131813777290606 : ((False ∧ (((p2 ∧ p2) ∧ (p5 ∨ False)) ∧ True)) ∨ (p1 ∨ (p4 ∨ (((p5 → p3) ∧ (p4 → (False ∧ True))) → (False → ((p3 ∧ p5) → p1)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_665090661625444381960370977169 : ((((p5 → ((((p2 → p3) ∧ (((((False → False) ∨ p5) ∧ p5) ∨ p3) → True)) ∧ p1) → (((p3 ∧ p1) ∧ p5) → p4))) → (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670183925729918273928625427602 : ((((((False → (p3 ∨ p5)) ∨ False) ∧ ((p2 ∧ False) ∨ (p2 ∨ ((p2 ∧ (p4 ∨ p2)) ∧ ((False → p3) ∨ p4))))) ∨ ((p5 ∧ p1) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300129670267784807291531442655 : (False ∨ (((p1 ∨ p5) ∨ (((p4 → (((((p5 → p2) → p5) ∨ True) ∧ (True → p1)) → (p4 → p2))) ∧ (p5 → p4)) ∧ p1)) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_750669654764659695816816636935 : (((True ∧ (((True → (p2 → (p5 → p3))) ∧ ((False ∧ (False ∨ (False ∧ False))) → (p3 ∧ p1))) → ((((True ∨ False) → False) ∧ p2) → p3))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h7 : (True ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299323173975182987757429664705 : (False ∨ (((((False ∨ p1) ∨ p3) ∧ p1) ∧ ((p3 ∨ p1) ∨ ((((False → p2) → ((p2 ∨ False) ∧ p4)) → p1) ∧ ((p5 ∧ p4) → False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776468753693278072021163873906 : (((p1 ∨ (((((((p4 ∨ p3) ∧ True) ∧ (p5 ∨ p2)) ∨ p3) ∨ (False ∧ ((p2 → p5) → ((p5 ∧ p5) → p3)))) ∨ (False ∨ p2)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208781256691617359652674032091 : ((p2 ∧ ((p1 ∨ p1) → (p3 ∨ p2))) → (((p2 ∧ ((p3 → ((p2 → p2) ∧ False)) → p3)) ∨ (False → True)) ∨ (p1 ∨ ((p4 ∧ p2) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809794271163927454582528331750 : (((p5 → (((False ∨ p2) ∨ (((((((True → False) ∧ p3) ∨ p5) ∧ ((p4 ∨ True) → (True → p4))) ∨ True) ∧ True) ∨ True)) ∨ (p4 ∨ p3))) ∨ p5) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135793294400155316743498703746 : (((((p5 ∧ True) → p5) → (p3 ∧ (False ∨ (((p4 ∨ p4) ∧ False) ∨ p5)))) → ((p3 → (False ∧ (p5 ∧ p4))) ∧ True)) ∨ (True → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777030628411642307074475452846 : (((p1 ∨ (((p4 → (True ∨ ((((((p3 → True) ∧ p4) ∨ (((p2 → True) ∧ p1) → p2)) ∧ p1) → p3) ∨ True))) → p2) ∨ (p2 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613837782750966343045416489920 : ((((((((((p4 ∨ p2) → (((p3 ∨ False) → True) → p4)) ∨ True) → p3) ∧ (p1 → (p2 ∧ p2))) ∧ True) ∨ ((p3 ∧ False) → p4)) ∨ p2) ∨ p2) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68153781592924999914283983691 : ((p3 → ((((((p3 ∨ p2) ∧ p1) ∨ p2) ∨ p4) → (False ∨ (False ∨ (((p5 ∧ p5) ∧ (p3 → p4)) → ((False → p5) → p1))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149785412762568407143508676872 : ((False ∨ ((((p4 ∧ p3) → (False → (p2 ∨ (p5 ∧ (p5 → False))))) → p1) ∨ (p5 → ((True → p4) → p4)))) ∨ (p5 → ((p5 ∧ p3) ∧ True))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54421769321793057403040741627 : (((((p3 ∨ (p3 ∨ (False ∨ p1))) ∨ p5) ∨ p3) ∨ (p4 → (p4 ∨ (p5 ∧ (False ∧ ((p5 → p4) → ((p5 → (p2 ∨ p1)) ∧ p5))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691642058553252014604267983286 : ((((p4 ∧ ((p1 → (((p5 → True) ∨ p5) ∧ (True → p3))) ∨ (p2 → (False → False)))) → ((((True ∨ p5) ∧ p1) ∧ p5) → (p3 ∨ p4))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h1.left
    let h9 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h1.left
    let h14 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591714389493520986516234463689 : (((((((((p5 ∧ ((p1 → True) ∨ p5)) ∧ ((((p5 ∧ p1) ∨ p1) → p3) ∧ p3)) ∧ (False → False)) ∧ p3) → p4) ∨ (p2 ∨ p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50292324906738524967967594481 : ((((((p3 ∧ False) ∧ p5) → ((p2 ∨ (True → ((p4 → p5) → p2))) → True)) ∧ (p2 → (p1 ∧ p5))) ∨ ((p4 ∨ (p2 ∨ p4)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721713453475595983451104920879 : ((((False ∨ (p5 ∨ (p5 → True))) → (True ∧ (True ∧ (True → ((p1 → ((True ∨ p1) ∧ False)) → (p1 ∧ (((False ∨ p1) ∧ p3) → p5))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53586425153871681602797998361 : (((((p1 ∨ (p4 → (False ∧ False))) ∧ (p4 ∨ p5)) → p4) ∧ ((p1 ∨ ((p5 → False) → (p2 ∨ (p4 → True)))) ∨ ((True ∨ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44105357777460978190420607484 : ((((((p2 → ((p3 → (p2 ∨ p5)) ∨ False)) ∧ ((p5 ∨ p4) → (p4 ∨ ((p2 ∨ p2) → p3)))) ∨ False) ∨ ((p4 ∨ p2) ∨ p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190035915023614767850063238663 : (((((p2 ∧ (p3 ∧ (p4 → p5))) ∨ p2) ∨ p1) ∧ False) ∨ (True ∨ (p5 ∨ (((((p4 → p1) ∧ p5) ∨ ((p3 → p2) ∨ p1)) ∧ p3) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190079275323557887214842455764 : ((((p1 → ((p1 ∧ (p2 ∧ p4)) ∧ p5)) → p3) ∧ p4) ∨ ((((((False ∧ p2) → False) → (p2 ∨ p3)) ∨ ((p3 ∧ p5) ∨ p3)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260683020047388914631000343263 : ((p3 → p3) → ((p5 → True) → (p5 → (((p4 → (p1 ∧ ((p1 → p2) ∨ ((p5 → (False ∧ p4)) → False)))) ∨ (p3 → True)) ∨ (p1 ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117653530022896366692165748692 : ((p3 ∧ (((True ∨ ((False → p5) ∧ (True ∧ True))) → ((((p3 → True) → (p2 → p4)) ∧ p3) → (False ∨ p4))) ∨ (p3 ∧ True))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39050828884805465554481910542 : ((((p1 ∧ p4) ∨ ((((p1 ∨ (True → p1)) ∨ p2) → (p5 ∨ (p1 ∧ ((True → ((p1 ∨ False) → True)) ∨ (True → p2))))) ∨ p1)) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218233394909606676497207283985 : (((p5 ∧ p3) ∨ (p4 → p4)) → (((False → p5) → p3) ∨ ((((p3 → True) ∧ p3) ∧ False) → (((p3 ∨ p2) → (p5 ∧ p3)) ∨ (p3 ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203931921996217924665591563919 : ((p2 → ((p3 ∨ (p4 ∧ p3)) → p3)) ∧ (((p5 → (p2 ∧ False)) ∧ (p5 ∨ p5)) → (False ∨ (False ∧ (p1 ∨ (p2 ∧ (p4 ∨ (True → True)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h11 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h12 := h8 h11
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h15 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h14
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h16 := h8 h15
    -- We need to get the right conjuct of h16 based on <expert-advice>.
    let h17 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165110621930279919491699922695 : (((p2 → (((p1 ∧ (((p4 ∨ False) → (p3 → p3)) ∨ p5)) ∧ p3) → (p4 ∨ p3))) → p5) ∨ ((p4 ∧ ((p2 ∧ False) ∨ (p5 → p1))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165649399153106235650407269098 : (((((p5 ∧ (False → p5)) ∨ False) ∨ p4) ∨ ((True → (p3 ∧ ((p3 ∨ p2) ∧ p2))) ∨ True)) ∨ (False ∧ ((p1 ∨ False) → (p2 ∨ (False ∨ p1))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658797393657832115580067533954 : ((((p5 ∨ (p2 ∨ ((p2 ∨ p4) ∨ ((((p4 ∧ p1) → p4) ∨ p1) ∧ (p5 ∧ (p3 → ((p2 ∨ False) → (p3 ∧ p4)))))))) ∨ (p2 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230356419767270223490056379953 : (((p2 ∨ p4) ∧ p4) → ((p4 ∧ (((p3 ∧ True) ∧ (p4 ∨ p3)) ∧ p3)) ∨ (p2 ∨ ((p2 → ((False ∧ p2) → False)) → (p3 → (p2 → True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356762890934959862990005535371 : (p5 → (((True → ((p3 ∧ p2) ∨ p5)) → True) → (True ∧ ((((p2 → ((p2 ∧ (False ∨ p2)) ∧ True)) ∧ (True → False)) ∧ p5) → (p3 ∧ p1))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- False on the left can always be used.
  apply False.elim h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
  have h14 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h13, we can now drive its conclusion.
  let h15 := h13 h14
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186174769821252824087041179789 : (((False ∧ (p4 ∨ ((True ∧ (False → (p3 ∧ True))) ∨ True))) ∨ p1) → (((p2 → p3) ∨ ((p2 ∨ ((p5 ∧ (p4 ∧ p3)) ∧ p4)) ∨ p2)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337520630818789522159625673514 : (p1 → (((((True ∧ (p5 → p3)) ∨ ((False → p2) ∨ ((((p5 ∧ p3) ∨ p1) ∧ p1) ∧ p4))) → p4) ∨ True) ∨ ((True → p1) ∧ (p4 → p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320312101496171016236742089163 : (p4 ∨ ((p1 ∨ p1) ∨ ((p1 ∨ ((p2 ∧ (False ∨ ((p1 → p1) ∨ p4))) ∨ ((p3 → (p3 ∨ ((p2 ∧ p1) ∨ (p1 ∨ False)))) → False))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802562502367147930976632743189 : (((p2 → (p4 ∨ (p1 ∧ (True ∧ (True ∨ (False ∧ (p3 ∨ (p4 → (((p1 ∨ p2) ∧ ((p1 ∨ (p5 → p2)) ∧ p5)) ∧ (p5 → True)))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186386637201872069806978136905 : (((p1 ∧ ((p1 ∧ (False → (False ∧ True))) → (p2 ∧ True))) → p2) → ((p5 → (p3 ∧ p1)) ∨ (True → (((True → False) ∨ (p3 ∨ p3)) ∨ True)))) := by
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
theorem thm_5_vars_763887070558624287807329349398 : (((p3 ∧ (p4 ∨ (p5 → (((p5 ∧ True) → p4) ∧ ((((p3 ∧ p4) → p5) ∧ ((False → (p1 ∨ (True → p2))) → p4)) ∨ (p4 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215286573256019413645733576521 : ((p1 ∧ ((p5 ∧ p5) ∧ p3)) ∨ (True → (p5 → (((((p3 → p1) → ((True ∨ p1) → ((True ∨ (p1 ∨ p3)) → p3))) ∧ p3) → p2) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228177882321453694937738721352 : ((p5 ∧ (p2 ∧ p1)) ∨ (((p3 ∨ p1) ∨ (True → (True ∨ True))) ∨ ((p5 → (p5 ∧ ((p2 ∨ p3) ∧ p5))) → ((p5 ∧ (p3 → p5)) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244280104173895317180329207660 : ((False ∧ True) ∨ ((p3 ∧ (False ∨ True)) ∨ ((((p4 ∧ p1) ∨ p2) ∨ ((True ∨ p4) ∧ p1)) ∨ (((p4 → True) → (False → (p2 → p1))) ∨ p2)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644506810429587914294246865482 : ((((p1 ∨ (((((((p3 ∨ False) ∧ p1) ∨ (p5 ∨ (p1 ∨ False))) ∨ True) ∨ p4) ∨ ((p3 ∨ (True ∨ (p2 ∧ p1))) ∧ p5)) ∨ p5)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62203694656933326956173738751 : ((p3 ∧ (((True ∧ ((True ∨ p2) ∧ p1)) → ((True → p3) ∨ (((p3 → p3) ∨ (((p2 → (False ∨ p1)) ∧ p1) ∧ p4)) ∧ p5))) ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59751519324224436406729794969 : (((p1 ∧ p2) → ((((False ∨ False) ∧ True) ∧ ((p3 ∨ p3) ∨ (p5 ∨ ((p5 ∨ True) → p4)))) ∨ ((p5 ∨ True) → ((False ∨ p2) ∨ True)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149396272005506458895216291702 : ((True ∧ (((p5 ∨ ((False ∧ False) ∧ (p1 ∧ ((((p5 ∧ False) ∨ p2) → (False ∧ p3)) ∧ p1)))) ∧ p5) ∨ False)) ∨ ((p1 → (p5 ∧ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



