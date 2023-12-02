variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114416572302258646013630161010 : ((((p2 → p4) ∧ (p2 → ((p1 ∨ p2) → (p3 ∨ ((p5 ∨ (p3 → (p4 → True))) → p5))))) ∨ (p5 → (True → (False ∨ True)))) ∨ (p5 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50814837684944124233847937511 : (((p4 → (((p5 ∧ (((((False ∧ p5) → p5) ∧ p1) → p2) → (False ∧ (p5 ∧ False)))) ∨ p1) → p2)) → ((p2 ∨ (p5 ∨ p5)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200730365928241764041554287220 : ((p3 ∧ (((False ∨ p1) → (p5 ∨ p3)) → p2)) → (p4 → (p4 ∧ ((((False ∧ False) → ((p5 ∧ p4) ∧ p5)) → (p1 ∧ p5)) ∨ (p4 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114266116578058910911439749728 : (((((((p4 ∨ True) ∧ (p3 → (p4 → p2))) → (p3 ∧ True)) ∨ ((p1 → p3) ∨ p5)) ∧ False) ∧ (p2 ∧ (False ∧ (True ∧ p4)))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671736789983086786489755061089 : ((((((True → ((True → p1) ∨ (((False ∨ False) ∧ p4) → ((p3 ∧ p3) ∧ p4)))) ∨ ((True ∧ p5) ∨ p4)) ∧ p1) → ((p4 ∧ True) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88011590678813754712012399434 : (((((False → p2) → False) ∧ p5) ∧ (((p4 ∨ p1) → p3) ∨ ((((p3 → (p5 → p4)) ∨ ((p3 ∨ p5) ∧ False)) ∧ p5) ∨ (p4 ∧ p1)))) → False) := by
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
    have h7 : (False → p2) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h15 : (False → p2) := by
          -- Implications on the right can always be decomposed.
          intro h16
          -- False on the left can always be used.
          apply False.elim h16
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h15
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h21 =>
          -- False on the left can always be used.
          apply False.elim h20
        case inr h22 =>
          -- False on the left can always be used.
          apply False.elim h20
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h26 : (False → p2) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- False on the left can always be used.
        apply False.elim h27
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h28 := h4 h26
      -- False on the left can always be used.
      apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613122893469163660522884007539 : ((((((p3 ∧ (p4 ∧ (((p5 → ((p3 ∧ p4) ∧ (p4 → p3))) ∨ p1) ∧ (((p4 → p2) → p2) ∨ p1)))) → p2) → (p4 ∧ p3)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199605964437073046990180254906 : ((((p2 ∧ ((p2 → False) → p1)) → p2) → False) → ((p2 ∧ p5) ∨ (p2 ∧ ((p5 → (p4 → (False ∨ p4))) ∧ (((p5 ∨ p1) → False) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ ((p2 → False) → p1)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187441234132809829849689650035 : ((p5 ∧ (p1 → (((p5 ∨ False) ∧ (p2 ∧ False)) ∨ (True ∧ False)))) → ((((True ∧ p5) → True) → (((p4 ∧ False) ∧ (p1 → p2)) ∧ p1)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204942119700001922879543266840 : ((((p3 ∨ p3) → (p3 ∧ p1)) → False) ∨ (p2 ∨ ((p4 → (p2 ∧ (((((True ∨ (p2 ∨ p2)) ∧ p4) → p1) ∨ (p3 ∧ p1)) ∨ p5))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44772887770609606992649936706 : ((((False ∧ (p1 ∨ (p4 ∨ p3))) → (((False ∧ (p2 ∧ True)) ∨ ((p4 ∨ ((p1 ∨ p5) ∧ ((p1 ∨ False) → p2))) ∨ p2)) ∨ True)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348532646304491160914612250677 : (p3 → (p3 ∧ (True → (((False ∨ (p5 ∧ (False ∨ (p3 ∧ False)))) ∧ False) ∨ (False ∨ (True → (((False → True) ∨ True) → (p3 → (p3 ∧ True))))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112884306551432923062092353456 : ((((p4 ∧ p1) ∧ ((((((((p3 ∧ p1) ∧ False) ∨ (p4 ∨ (p4 ∧ True))) ∨ p4) ∧ p3) → False) → (p4 ∨ p2)) → p5)) → p3) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258173131474532806687702779020 : ((p4 ∨ p4) → ((((((False ∧ p1) ∨ p2) → (p3 ∧ p1)) → p4) → ((((p5 → (p4 → p3)) → p2) ∧ True) ∧ p1)) → (p5 → (p1 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((((False ∧ p1) ∨ p2) → (p3 ∧ p1)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((((False ∧ p1) ∨ p2) → (p3 ∧ p1)) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h12 := h2 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h13
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756265833823850557608117993780 : (((p1 ∧ (((((p1 → True) ∨ ((p1 ∧ ((((False ∨ p5) ∨ p1) ∨ p1) → p5)) ∨ False)) ∧ (p5 ∨ (p5 → p2))) ∨ False) → (p3 → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105100110694646133653817150575 : ((((((p3 ∧ (True → (p3 → ((False ∨ (p3 ∧ p2)) ∨ (p5 ∧ p4))))) → (p4 ∨ True)) ∨ p4) → p5) ∨ ((True → False) → p5)) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60525833831876607299430784676 : ((True ∧ (((p2 ∧ (((((p2 → p5) ∨ p1) ∨ p5) → p2) ∧ (((p2 ∧ True) → (p2 ∨ (p3 ∨ p4))) ∨ (p4 ∨ False)))) ∨ False) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164523513625403689805937325107 : ((((((True → (p5 ∧ (p2 ∧ True))) → p1) ∧ ((p3 → p3) ∨ False)) → (False ∧ False)) ∧ True) ∨ (((False ∧ (p2 ∨ (p5 ∧ p2))) ∧ p1) → p5)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251419519640396246892548566029 : ((p2 → p5) ∨ ((p5 → (((p5 ∧ ((((p2 ∧ p5) → p3) ∧ p5) → p4)) → p2) ∨ (((p5 → p2) ∨ (p1 → (False ∧ p2))) ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636527756410040814206092386937 : (((((((p1 ∨ ((p1 ∧ p4) → p3)) ∨ False) → (((True ∨ p5) ∧ p1) ∧ p3)) ∧ ((p3 ∧ ((p4 ∧ False) → (p4 → True))) ∨ p2)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200092210735654422004191022993 : ((((p3 ∧ True) → p1) ∧ (p3 → (False ∨ p5))) → ((p4 ∧ (p1 ∧ (p1 ∧ p3))) ∨ (p3 → (p1 ∨ ((True ∨ p5) ∧ (p3 ∨ (True ∧ p5))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657688738922885579753641050043 : (((((False → p3) → (((True → p3) ∨ ((((p4 ∧ p1) → p2) ∨ (p5 ∧ p1)) ∨ (p1 ∨ (p5 ∧ (p2 ∧ p5))))) ∨ p5)) ∨ (p3 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256903636393589601043144168694 : ((p1 ∨ p4) → (((p2 → (p1 ∨ (True → ((p5 → False) ∧ p3)))) ∧ (True → p2)) ∨ (p4 → ((p1 → p3) ∨ (p3 ∨ (p1 ∨ (p4 → True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257746556755531138495307897427 : ((p3 ∨ p4) → ((p2 ∨ ((p5 ∧ p2) ∨ ((p3 ∨ p4) ∧ (p4 ∨ (((p5 ∧ (p2 ∧ p5)) → (True → True)) → True))))) ∧ (True ∨ (p3 ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178321011767369411674024117568 : ((((p3 ∨ (p3 → ((p3 ∨ (p3 → False)) ∧ p1))) → p4) ∨ (p3 → p1)) ∨ (((p5 ∨ p2) ∧ (p5 ∨ ((p4 ∨ False) ∨ False))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116336236478553307031273986829 : ((((p2 → p1) ∧ p5) → ((((p3 ∧ (True ∧ p2)) ∨ p5) ∧ (p1 → (p5 ∧ (p4 ∧ (p5 → p1))))) → (p3 → (p5 ∧ p1)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659297665609844471199753470959 : ((((p5 → ((((p3 → p2) ∨ ((((p2 ∧ p3) ∧ p2) ∨ ((p3 → p1) ∧ True)) ∧ p5)) ∨ (p4 ∨ False)) → (p2 ∧ False))) ∨ (False → p4)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_57988250005355575096538460407 : (((p4 → (p4 → False)) → ((p1 ∨ p1) → ((((((p3 ∧ p1) ∨ ((p2 → p4) → False)) ∨ (p4 ∧ p1)) ∧ p5) ∨ p1) ∧ (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197943155077473443781790044548 : (((False ∧ p5) ∧ (True ∨ (p1 ∨ (True → p4)))) ∨ (((p4 ∧ True) ∨ ((False → p3) → (p3 ∧ ((p5 → (p3 → False)) → p3)))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1091215669611355965993217625 : (((((p5 → False) ∨ (((p3 ∨ (((False → p3) → p3) ∨ p1)) → (False ∧ p5)) → True)) ∨ p5) → ((p2 → (p3 ∧ True)) ∧ p2)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 → False) ∨ (((p3 ∨ (((False → p3) → p3) ∨ p1)) → (False ∧ p5)) → True)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601913697264454030022381257632 : ((((p4 ∧ (p1 ∧ ((((False ∧ p1) → (((p4 ∧ (p2 → p4)) → p2) ∧ (True ∨ p4))) ∧ (True ∧ (p4 → p4))) → (p4 ∨ p3)))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733132704095566712470115923830 : ((((p3 ∧ False) ∧ ((p1 ∧ False) ∨ ((True ∨ p3) ∧ (p3 ∨ ((False → (p2 ∧ p2)) ∨ ((p1 ∧ p3) ∧ (p3 ∨ (p3 → (p4 ∧ True))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614518494186988506124778616596 : ((((((False → (True → (p4 → ((p2 ∧ p2) ∨ (((True ∨ False) ∨ p2) ∨ p4))))) → (p5 → p3)) ∧ ((p4 → (True ∨ p5)) → p5)) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49123412022380182667267212468 : (((((True → ((p5 ∧ (False → (True ∧ p5))) ∧ p5)) → (p4 ∧ p1)) ∧ (((p2 ∨ (p1 → p2)) ∧ p2) ∧ True)) ∨ ((True ∨ p4) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231720468725238861752861134466 : (((p2 ∧ p2) → p1) → ((((False ∨ p1) ∧ p5) → p4) ∨ ((p1 ∨ (((p4 → p1) ∨ p2) ∧ True)) ∨ (False ∨ ((p3 ∨ p3) → (False → p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783748426400143888976067196568 : (((p3 ∨ ((p1 → (p4 → (True → (False ∧ p4)))) → (p5 → ((False ∨ (((True → p3) → (False ∨ p3)) ∧ (p2 ∧ False))) ∨ (p5 ∨ True))))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_752578754281133933339381337366 : (((False ∧ (((((p5 ∨ p2) ∨ ((True ∧ ((p2 ∧ ((True ∧ p1) → p4)) ∧ True)) ∨ (p4 → ((p3 ∨ True) ∨ True)))) ∨ p5) ∧ p1) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603900165402854428256520399811 : ((((p4 ∨ (p3 → (((False ∨ p5) ∨ ((p4 ∨ (((p3 ∧ p3) ∨ ((p2 ∧ False) → ((p2 → p5) → p5))) ∨ True)) → True)) ∧ False))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636099211505943773291769037294 : (((((((((True ∨ (False ∧ False)) ∧ p5) ∨ ((False → p1) → (False → True))) ∧ p2) ∧ p2) ∨ (p2 → (p3 ∨ ((p4 ∨ p2) → p4)))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56933703416998650692502345846 : (((False ∨ (p3 ∧ p5)) ∧ ((False → (((p4 → p4) ∧ ((True → (p4 → p5)) → ((True ∧ p1) → p5))) ∨ p1)) ∧ (p4 ∧ (p3 ∧ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47747056178383678061767096891 : (((((False ∨ ((p1 ∨ True) ∧ p4)) ∧ ((((False ∨ p2) ∨ (p5 → True)) ∨ (p5 ∧ ((p1 ∧ False) → p2))) ∨ False)) ∨ False) → (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59991382946720582544193147358 : (((False ∨ p3) → ((((True ∧ p1) ∧ (((True ∧ p1) ∨ p3) ∨ (((False ∧ p4) ∧ (p1 ∨ p1)) ∧ (p2 ∧ (p5 ∨ True))))) ∨ p1) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301138716156257555734987776290 : (False ∨ ((((p5 ∨ (p2 ∨ (p2 → p3))) → p5) ∨ False) ∨ (((p4 → (False → (p2 ∧ p2))) ∨ p3) → (p5 ∨ (p4 ∨ ((p4 ∧ p4) ∨ True)))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764608501184621498693914582320 : (((p4 ∧ ((((((p4 ∨ p2) ∧ (p1 ∨ False)) ∧ (p1 ∨ False)) ∧ (p4 → p1)) ∨ (False ∨ (((False ∨ True) → p5) ∧ (False → p2)))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355579278130842883133492049362 : (p5 → ((((p4 → (p4 → p1)) ∨ ((p2 → ((p3 → False) → (True ∨ p3))) → p4)) ∨ ((((p2 ∧ p3) → p2) → True) ∨ False)) ∨ (p3 ∨ p4))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657792801088392752606510112699 : ((((True ∧ (p1 ∨ ((p2 ∨ (((((p3 ∧ True) → p2) ∨ p2) ∨ ((p4 ∧ ((p2 ∨ p2) → p3)) ∨ p2)) → p1)) ∧ p2))) ∨ (p1 → p1)) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199236391580643927669139613133 : (((False → ((False ∧ p3) ∧ (p2 ∧ p2))) ∧ p1) → (((((p5 ∨ p3) → False) ∧ p5) ∨ ((((p3 ∧ p5) → (False → False)) → p5) ∨ True)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111056942380509422264397024079 : ((((p4 → (((p3 ∧ p1) ∧ (p2 ∨ p1)) ∨ (((p2 → (p4 ∧ False)) ∨ p2) ∨ p4))) → (p2 → (p4 ∨ (p3 ∧ p2)))) ∧ p4) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57147108286989721855261714083 : ((((p4 → p4) ∧ p2) ∨ (True ∧ (p3 ∧ ((((True → ((p5 ∨ (p4 ∨ p5)) ∨ p4)) ∧ (p5 ∧ (False → False))) → (True ∧ p3)) → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116244809584566421530931945072 : ((((p5 ∨ p1) → p2) ∨ ((p1 ∧ (p2 ∧ (p3 ∧ ((False → False) → False)))) ∧ ((p5 ∨ (p3 → ((p4 ∧ p5) ∧ False))) ∨ p1))) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123396116291250771199895633318 : ((((((p1 → p5) → ((False ∨ p5) ∨ ((p5 → p4) → (p5 ∧ (p1 → False))))) ∨ p2) → p4) → ((p3 ∧ True) ∧ (p2 ∧ p5))) → (p4 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((p1 → p5) → ((False ∨ p5) ∨ ((p5 → p4) → (p5 ∧ (p1 → False))))) ∨ p2) → p4) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h3
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319457614675022362560015324162 : (p4 ∨ ((((((p5 ∧ p4) ∧ p3) → p4) ∧ False) ∨ (False ∧ (p1 ∨ p2))) ∨ (False ∨ (p1 ∨ (((True ∨ p1) ∨ ((p2 ∨ p3) ∨ p5)) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159994848568709714123400373637 : ((((p1 ∧ (False ∨ ((p4 → p3) ∧ p1))) ∧ (((p4 → (p5 → p3)) ∨ (p2 ∧ p5)) → p2)) → p2) → (p3 ∨ (p3 ∨ (p1 → (p2 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61146711779436024420342529740 : ((False ∧ ((p1 → (((p1 ∨ p4) ∧ p4) ∧ True)) → (((((p1 → p4) ∨ (p5 ∨ p2)) ∨ (False → False)) → ((p2 ∨ True) → p5)) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740891778199376964248982124749 : ((((p3 ∨ p1) ∨ (p4 ∧ ((((p2 ∧ (p1 ∧ True)) ∨ (p1 ∧ p1)) ∨ ((p1 ∨ (p1 ∧ (True ∨ p3))) → p1)) ∨ ((True ∧ p3) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349062538785261634882588794827 : (p3 → (p5 ∨ ((True ∨ (p1 ∨ p3)) → ((p2 ∨ p1) ∨ (((p2 ∨ (p2 ∨ (p5 → (p2 ∧ (p3 ∧ False))))) ∧ (False ∧ True)) → (True → p1)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h7.left
      let h10 := h7.right
      -- False on the left can always be used.
      apply False.elim h9
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h7.left
        let h14 := h7.right
        -- False on the left can always be used.
        apply False.elim h13
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h7.left
        let h17 := h7.right
        -- False on the left can always be used.
        apply False.elim h16
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h19
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h24.left
        let h27 := h24.right
        -- False on the left can always be used.
        apply False.elim h26
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h28
        case inl h29 =>
          -- Conjunctions on the left can always be decomposed.
          let h30 := h24.left
          let h31 := h24.right
          -- False on the left can always be used.
          apply False.elim h30
        case inr h32 =>
          -- Conjunctions on the left can always be decomposed.
          let h33 := h24.left
          let h34 := h24.right
          -- False on the left can always be used.
          apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200101349731027675388997326281 : ((((p4 → p2) → False) ∧ (p2 ∨ (p4 ∧ False))) → (p4 ∨ (p1 ∨ ((((((True → p5) ∧ False) ∧ p5) ∧ p4) → ((p4 ∧ True) ∨ p2)) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (p4 → p2) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319276834575024998874113876344 : (p4 ∨ (((p1 ∨ (((p1 ∨ p2) → p5) → p5)) ∧ (((p4 ∧ p2) ∨ (p5 ∧ p3)) ∧ p1)) ∨ (p5 → (p3 → (p4 ∨ ((False → p3) ∨ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56471825116405051892543868134 : ((((p4 ∨ p2) → (p3 ∧ p5)) → ((((p5 → ((p4 → p3) ∧ (p5 ∧ p5))) ∧ True) → ((False ∨ (p1 ∧ True)) ∧ p3)) ∨ (True ∨ False))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2374069826101071213386413853 : ((((False ∨ p3) ∨ p4) ∧ (p2 → (p5 ∨ ((p1 ∧ False) ∨ p1)))) ∨ (((False ∧ ((((p2 ∧ p1) ∧ False) ∨ False) ∧ p4)) ∧ p5) → p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765953585088643982551418984590 : (((p4 ∧ ((p5 ∨ (False ∨ (False ∧ p5))) ∨ (((((p5 ∧ True) → p2) ∧ (True ∧ p2)) ∧ (p1 ∧ ((p2 → (p5 ∧ p4)) ∨ False))) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172742450998132073767658510099 : (((True ∧ p1) → ((True ∨ (p3 → (p3 ∧ (p4 → ((p5 ∧ True) → p2))))) → False)) ∨ ((True ∧ p1) ∨ (p4 → (p1 ∨ ((p2 ∨ p2) ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_134507520529051843417821176515 : (((((p2 ∨ p4) ∧ ((p2 → p4) ∧ (False ∨ ((p5 ∨ ((((p4 → p4) → p3) ∨ p1) ∧ True)) ∧ p2)))) ∨ p2) → p1) ∨ (p1 ∨ (False → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214183373173578052642736558640 : ((((p1 ∨ p3) → p5) → p2) ∨ (((((p4 ∨ p4) → (((p3 ∧ p5) ∧ p5) → p2)) ∧ (p1 ∨ p1)) ∧ (((False → p1) ∧ False) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47030784911759825477105671463 : ((((p5 → ((p2 → ((False ∧ p2) → p5)) ∨ (p3 → (((((p4 ∧ (p5 → p1)) → False) ∧ p5) ∨ False) ∧ p1)))) → p4) ∨ (p2 → p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148659904583923757860889805729 : (((p4 ∧ (((True → p2) ∧ p4) ∧ (True ∧ p2))) ∧ ((p5 ∧ False) ∧ ((p3 ∨ True) ∧ ((p4 ∧ p4) ∧ p1)))) ∨ ((p4 → True) ∨ (p2 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46816070353974446828520061383 : ((((((((False ∨ p3) ∨ (p1 ∧ (False ∨ False))) → (((p5 ∨ True) ∧ False) ∧ (True ∧ (p5 ∨ p2)))) → True) → p5) ∧ p2) ∨ (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672126390285050076992351839054 : ((((((p4 ∨ p3) ∨ (((True ∧ (False ∧ (p2 ∨ p5))) ∨ p4) → (((p1 ∨ False) ∧ p1) ∨ (False ∧ True)))) ∨ False) → (p1 ∨ (p3 ∨ True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172791465617101155710705761568 : (((p1 → p3) → ((False ∨ p3) ∨ (((True ∧ (p4 → (False ∨ p5))) → True) → False))) ∨ ((False ∨ False) → (False ∨ (((p4 ∧ p3) ∧ p5) ∧ p3)))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300686159550438901070784783882 : (False ∨ (((p3 ∧ False) ∨ (p4 ∧ ((p3 ∧ (p1 ∨ (False ∧ ((p5 ∧ False) → (p4 → p1))))) ∨ True))) ∨ (True → ((p3 → (p3 ∨ False)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111889502572538545033967165348 : ((((p4 ∧ ((p1 ∨ (p4 → (p1 ∨ (False ∨ p5)))) ∨ (p4 → (p1 → p2)))) ∧ (p4 → (((p5 ∨ False) ∧ False) ∨ p5))) ∨ True) ∨ (False ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113023309644659114824967059391 : (((True ∨ ((p5 ∨ ((p2 ∧ ((((p2 ∨ p1) → (p3 → p2)) → p4) ∨ ((False ∧ p4) ∨ (p2 ∨ False)))) ∨ True)) ∨ p4)) → p5) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137782054125855934397480130337 : ((p2 ∨ ((False → (p3 ∨ False)) ∧ ((True ∧ ((p3 ∧ (False ∧ ((((True → p3) ∨ p3) ∨ True) ∨ True))) ∨ p5)) ∧ p3))) ∨ (True ∧ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51797830914112784673474032423 : (((p1 ∨ ((((p4 → (False ∧ p2)) → False) ∧ (False ∨ (p4 → False))) ∨ (p1 → False))) ∧ ((p2 ∨ ((True → p3) → False)) ∨ (p1 → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257416877382497037623132847431 : ((p2 ∨ p5) → (p1 → (((p4 ∨ (p1 ∨ (((p1 ∧ ((p3 ∧ False) ∧ p1)) → (True ∧ p4)) ∨ p2))) ∧ p4) → (p4 → ((p1 → False) ∨ p4))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
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
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h19 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191353466924963060776485091280 : (((p2 ∨ p4) ∨ (((p4 ∨ (p2 ∨ True)) ∧ p5) ∧ False)) ∨ (p4 ∨ (((p4 → (True ∨ False)) ∨ (False ∨ True)) ∨ (((True ∧ p2) → False) → True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139523052410055440310479774044 : ((((False → (p2 ∧ ((((True → (p1 → p3)) ∨ ((False ∧ False) → (p5 ∧ (p1 ∨ True)))) ∨ p5) → p5))) → p2) → p4) → (p5 → (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779978035772799056164053242132 : (((p2 ∨ ((True → (((p2 ∧ p4) ∧ p3) ∧ (((((p5 ∧ p3) ∧ ((p3 → p5) → False)) → p2) → (p2 ∧ p1)) ∧ True))) ∧ (p1 ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173501223970143159125198615491 : (((((p3 ∧ (p1 → p5)) → (((p1 → p3) ∧ p5) ∧ p4)) ∧ (True → p3)) ∧ p5) → (p2 → ((p3 ∨ (p3 ∧ (p5 ∧ False))) ∨ (p4 ∧ p3)))) := by
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
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683979904572182557138783643926 : ((((((((False ∨ (True → (p1 ∨ p1))) ∧ True) ∨ (p5 → p2)) ∨ (p3 ∨ (True ∨ p5))) → False) ∨ ((p4 ∨ (False ∨ p2)) ∨ (p1 → True))) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_249244792471478935194959663010 : ((p4 ∨ p4) ∨ (((((p4 ∧ (p1 ∨ (p1 → p4))) ∧ p3) ∨ ((p1 ∧ (p3 → p3)) ∧ (p5 ∨ p3))) ∧ (p2 → p5)) ∨ ((False → p2) ∨ p4))) := by
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
theorem thm_5_vars_185587684761872143911619409607 : ((p5 ∨ (((False → (p3 → p2)) ∧ (True → p5)) → (p2 ∧ True))) ∨ ((True → (p2 ∨ (p2 → (((p5 ∨ True) → (True ∧ p2)) ∨ p1)))) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64059039717325460250108449679 : ((False ∨ ((p4 ∨ (((False ∧ p5) ∧ ((((p2 → ((p4 ∧ p1) → p1)) ∧ p3) ∧ p4) ∧ True)) ∧ False)) ∨ ((p4 ∧ p3) ∧ (True ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337090044766648957729397125574 : (p1 → ((((True → ((False ∧ p4) ∨ p3)) → ((p5 ∧ p4) ∨ (p3 ∧ p5))) ∨ (p2 → (((p1 ∨ False) ∨ True) → (False → p3)))) ∨ (p1 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112414029127313917065320651057 : ((((p1 ∨ ((p4 → (p5 ∨ ((((False ∨ (p2 ∨ True)) ∧ False) ∨ (p3 → p3)) ∨ ((p3 → p4) ∨ p2)))) → p3)) ∧ p2) → p5) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_808582267127890741039188927579 : (((p4 → (True → ((((p3 ∨ p1) ∨ (p4 → ((p2 → p3) ∨ p1))) → p3) ∧ ((True → ((True ∨ (True → p4)) ∨ p2)) ∨ (p2 → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_689567682080563669018815781336 : (((((p3 ∨ ((p4 → False) ∧ ((p3 ∨ p4) ∨ p1))) → (True → (p2 ∧ (False ∧ p3)))) ∨ ((False ∨ p2) ∨ (p2 ∨ ((False ∧ p5) → p3)))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41639887160908515714105791830 : (((((((p1 ∨ p5) ∨ p1) ∨ True) ∧ p4) ∧ (p5 ∧ (True ∨ ((p5 ∧ p5) → (p2 ∨ ((p1 ∧ p5) ∧ ((p3 ∧ p5) ∧ p5))))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_145016463872457839685825857648 : ((((((p4 ∧ p1) ∨ p5) ∨ (p5 ∧ (False ∧ p3))) ∧ (p4 → True)) ∨ (((p1 → (p5 ∨ False)) ∧ p2) → p2)) ∧ ((False → (p5 → p5)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_923989206329887900760919823539 : ((((p2 ∧ (((((p2 ∧ p1) ∧ p3) → (p2 ∧ p1)) → p5) → False)) ∧ (((p4 → (False → True)) → p4) ∨ ((p5 ∧ (p1 ∨ True)) ∧ p2))) → p4) ∧ True) := by
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
  cases h3
  case inl h6 =>
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p4 → (False → True)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h10 := h6 h7
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h12.left
    let h15 := h12.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h17 : ((((p2 ∧ p1) ∧ p3) → (p2 ∧ p1)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h19 := h5 h17
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h21 : ((((p2 ∧ p1) ∧ p3) → (p2 ∧ p1)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h23 := h5 h21
      -- False on the left can always be used.
      apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116831753396364211887053262138 : (((p5 ∨ p4) ∨ (((((p3 ∨ p2) ∨ (p1 ∨ p4)) ∧ ((p3 ∨ ((((p1 ∧ True) ∨ p2) ∧ False) → p2)) → False)) → False) ∨ p4)) ∨ (True → p2)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : (p3 ∨ ((((p1 ∧ True) ∨ p2) ∧ False) → p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h7 := h3 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p3 ∨ ((((p1 ∧ True) ∨ p2) ∧ False) → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- False on the left can always be used.
          apply False.elim h12
        case inr h16 =>
          -- False on the left can always be used.
          apply False.elim h12
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h9
      -- False on the left can always be used.
      apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (p3 ∨ ((((p1 ∧ True) ∨ p2) ∧ False) → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h21
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h24 =>
          -- Conjunctions on the left can always be decomposed.
          let h25 := h24.left
          let h26 := h24.right
          -- False on the left can always be used.
          apply False.elim h23
        case inr h27 =>
          -- False on the left can always be used.
          apply False.elim h23
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h28 := h3 h20
      -- False on the left can always be used.
      apply False.elim h28
    case inr h29 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h30 : (p3 ∨ ((((p1 ∧ True) ∨ p2) ∧ False) → p2)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h31
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h32
        case inl h34 =>
          -- Conjunctions on the left can always be decomposed.
          let h35 := h34.left
          let h36 := h34.right
          -- False on the left can always be used.
          apply False.elim h33
        case inr h37 =>
          -- False on the left can always be used.
          apply False.elim h33
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h38 := h3 h30
      -- False on the left can always be used.
      apply False.elim h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621270943168451930086756991485 : ((((True ∧ (((p2 ∧ (p2 ∨ (p1 → ((p3 ∨ (p1 → ((p5 ∨ False) ∨ p3))) ∧ p3)))) ∧ True) ∧ (((True → p1) ∨ p1) ∨ False))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63346538985686560817599234772 : ((p5 ∧ (False ∧ (((p5 ∨ p3) ∨ (p1 → False)) ∨ ((((True ∧ p4) → (False ∧ p2)) ∧ (p3 → (False ∨ True))) ∨ ((p2 ∧ p3) ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356994507608014475850520527412 : (p5 → (((False ∧ p1) ∧ p3) ∨ (((((p4 ∨ True) ∧ (False → (True ∧ p4))) ∧ p4) → (p2 ∧ p3)) ∨ (((p1 ∨ p1) ∧ False) ∨ (p3 → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165639038048260034548575062250 : (((True ∨ ((True → (p5 ∧ p3)) → p2)) ∧ (((p4 ∨ (p1 ∧ p5)) ∨ (p3 → p4)) ∨ p2)) ∨ ((True ∧ p3) → (((p5 → p5) → p4) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_263446579957726541763875783667 : (True ∧ (((((((((p4 ∨ False) ∨ (((p3 ∨ (p2 → p4)) ∨ False) ∨ p3)) ∧ p1) ∨ p5) ∨ True) ∨ p2) ∨ p5) → False) → ((p1 ∧ p4) ∨ False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p4 ∨ False) ∨ (((p3 ∨ (p2 → p4)) ∨ False) ∨ p3)) ∧ p1) ∨ p5) ∨ True) ∨ p2) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49255634042316343315261688919 : (((False ∧ ((((p1 ∧ True) ∨ (p4 ∧ (p2 → ((p4 ∨ True) ∨ True)))) ∨ (False ∨ (p5 ∨ (p4 → p2)))) → False)) ∨ (p5 ∧ (p5 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663499898500895915516345874698 : (((((p4 → True) → ((((((p1 ∧ (p3 ∨ (p3 ∧ p5))) ∧ ((p1 → (p1 → False)) ∧ p2)) ∨ p3) ∨ p1) → p4) → True)) → (p3 ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301594276205473529297197661390 : (False ∨ (((p5 → p4) ∧ p4) → (((((p2 ∧ (True → (False ∨ p3))) ∧ p3) ∨ p5) ∨ True) ∨ (p4 ∧ (((p1 ∧ True) → False) ∨ (False ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312998011525842189317965964731 : (p3 ∨ ((((((True ∨ (p2 ∨ (((True ∨ (((False → (p2 → p5)) ∧ p4) ∧ True)) ∨ False) → p1))) ∧ p1) ∧ (p1 ∨ p4)) → False) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



