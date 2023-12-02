variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149243061989748412066079651194 : (((False ∨ p3) ∨ (((False → p3) ∨ p3) ∧ ((p1 ∨ (p1 ∨ (((p1 → False) → False) ∧ p4))) ∧ (p5 ∨ False)))) ∨ (True ∨ ((p5 → p5) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246738046527574044655611774284 : ((p5 ∧ p5) ∨ ((((p1 → (False → (p4 ∨ p1))) ∧ (p3 → ((((True → p2) → True) ∨ (((p3 ∨ p1) → p4) → True)) → p2))) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190239650964593579083013720660 : ((((((p3 → (p5 ∧ p5)) ∨ True) → p1) ∧ p1) ∨ p1) ∨ ((True ∧ ((False ∧ p5) ∧ p2)) ∨ (False → (p1 ∨ (p5 → (p2 → (False ∨ p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64440247156854064890976479711 : ((p1 ∨ ((((p2 ∧ p4) → (((True ∧ p4) ∧ p5) ∨ ((True ∨ p3) ∨ True))) → ((p5 ∨ (p2 ∨ (p4 ∧ p5))) ∧ False)) ∨ (False → p2))) ∨ p1) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166183476676796349303170331330 : ((p1 ∧ ((((p3 ∧ p1) ∨ (p2 ∨ p2)) → (p5 ∨ ((False ∨ p2) ∨ (p5 ∧ False)))) ∨ p4)) ∨ ((False ∧ (p2 ∨ False)) → ((p1 → False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48002702221627012450293364263 : ((((((((p2 ∧ p4) ∧ (p2 → p5)) ∨ (p2 ∨ (p2 ∧ p4))) → p5) ∧ p2) → ((p5 ∧ (p4 ∨ p3)) → (p2 ∧ False))) → (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258774841931147829647554293962 : ((True → False) → ((p3 ∨ ((((p2 ∧ (p4 → (p2 ∨ ((((p5 ∧ False) ∧ p2) ∨ p3) ∧ False)))) → p5) ∨ p5) ∧ (p3 → p4))) ∧ (p4 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346608167334150980709509660628 : (p3 → (((p5 ∨ (((p5 → True) ∨ (p5 ∧ True)) ∧ ((p1 ∧ p4) ∨ (True ∧ (p1 ∧ p3))))) ∨ (p2 → (False ∨ p2))) ∨ ((p3 → p2) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57291443839335384554129324495 : ((((p2 → True) → p2) ∨ (p1 ∨ ((((p1 → p5) ∧ (p4 → p1)) ∧ p5) ∨ ((True → ((p3 ∧ p1) ∧ p4)) ∨ ((False → p5) ∨ p1))))) ∨ p4) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181048038090065842560623675464 : (((False ∧ p4) → ((p3 ∧ (((p5 ∧ p4) → (p4 ∨ p2)) → p1)) → p1)) → ((((p5 ∨ (p5 → p2)) ∧ (p3 ∧ p1)) ∧ p4) ∨ (p1 → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41568733464934745928699487550 : ((((False ∨ (p4 → ((((p1 ∨ p5) ∨ False) ∨ p4) ∨ p3))) → (p4 → ((True ∧ (p4 → (p5 ∧ p1))) → ((p3 ∨ p4) → p1)))) ∨ p2) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h3.left
    let h7 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h18 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h19 := h15 h18
      -- We need to get the right conjuct of h19 based on <expert-advice>.
      let h20 := h19.right
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148005478302680209359350061545 : ((((((p1 ∧ ((p5 ∨ p2) → ((True → (p2 ∧ p2)) ∧ False))) → p5) ∨ True) ∨ (p4 ∧ p5)) ∨ (p5 → p1)) ∨ ((p2 → p5) ∧ (False ∧ True))) := by
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
theorem thm_5_vars_47189276651792413399452123839 : ((((p5 ∨ (((p3 ∧ ((p3 → p5) ∨ False)) → False) ∨ (True ∧ p4))) ∧ ((p2 → ((p3 ∨ False) ∧ p2)) ∨ (p5 → True))) ∨ (p4 ∨ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19603470495580091208502480934 : (((((False → p3) → False) ∧ ((((False ∧ p3) ∧ True) ∧ False) ∨ ((False ∧ True) ∧ p5))) ∨ (p1 ∨ ((True → p1) → ((False ∧ p3) ∨ p1)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40464269917778981906978496337 : (((((False ∨ (False → False)) ∧ ((p5 ∨ ((False → p4) ∧ (((p3 ∧ p2) → ((False ∧ p2) ∧ p5)) → p5))) → (p5 ∨ p5))) ∨ p2) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315820841039402159562392858457 : (p3 ∨ ((p3 ∨ p4) → ((((p5 ∨ (p4 ∧ (p4 ∨ ((p4 → p1) ∧ p3)))) ∧ (p1 ∧ True)) ∧ (((False ∨ (p2 ∧ p4)) → p2) ∨ p3)) → p1))) := by
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
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h11 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h15 =>
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- Disjunctions on the left can always be decomposed.
    cases h18
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h6.left
      let h21 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h20
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- One of the premise coincides with the conclusion.
          exact h20
        case inr h27 =>
          -- One of the premise coincides with the conclusion.
          exact h20
    case inr h28 =>
      -- Conjunctions on the left can always be decomposed.
      let h29 := h28.left
      let h30 := h28.right
      -- Conjunctions on the left can always be decomposed.
      let h31 := h6.left
      let h32 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h34 =>
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h35 =>
          -- One of the premise coincides with the conclusion.
          exact h31
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h31
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84040099983239672346626504657 : (((((p2 ∧ p5) ∨ (((p5 ∨ p4) ∧ ((p3 → p5) → True)) → True)) ∧ (True → False)) ∧ ((p5 ∧ ((True → p4) ∨ False)) → (p1 → False))) → p4) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h10 := h5 h9
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h12 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h13 := h5 h12
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48972762661500024972986049535 : ((((((p4 ∧ True) → (((p4 ∧ (False → ((p5 → p2) ∧ p1))) → p3) ∨ (p5 ∨ p3))) ∧ (p2 ∨ p3)) ∨ p5) ∨ (p5 ∧ (p4 ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710406496629222478079607380432 : ((((((p1 ∧ False) ∧ (p3 ∧ p3)) → p1) ∧ (p5 → ((p3 → ((p4 ∧ (p1 → p5)) ∨ (((True ∧ p2) ∨ (p4 ∨ p4)) ∨ False))) → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308534122797049027256182858830 : (p2 ∨ ((((((p4 → p5) ∨ (p2 ∨ (False ∧ (p2 ∨ p1)))) ∨ p5) ∨ p2) ∨ (False ∧ ((p5 ∨ (False ∨ (False ∧ p2))) → (p1 ∧ True)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180614221920904266453472135581 : ((((p5 → False) ∧ ((p1 ∨ p2) ∨ True)) ∧ (p5 ∨ ((p1 → p2) → False))) → ((p5 → p1) ∧ (p5 → (((p4 ∧ p2) ∧ p4) → (p4 → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h12 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h13 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h14 := h5 h13
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h16 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h17 := h5 h16
        -- False on the left can always be used.
        apply False.elim h17
  case inr h18 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h19 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h20 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h21 := h5 h20
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h2
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h24 := h5 h23
      -- False on the left can always be used.
      apply False.elim h24
  -- Implications on the right can always be decomposed.
  intro h25
  -- Implications on the right can always be decomposed.
  intro h26
  -- Implications on the right can always be decomposed.
  intro h27
  -- Conjunctions on the left can always be decomposed.
  let h28 := h26.left
  let h29 := h26.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Conjunctions on the left can always be decomposed.
  let h32 := h1.left
  let h33 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h34 := h32.left
  let h35 := h32.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h37 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h38 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h39 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h40 := h34 h39
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h42 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h43 := h34 h42
        -- False on the left can always be used.
        apply False.elim h43
    case inr h44 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h45 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h46 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h47 := h34 h46
        -- False on the left can always be used.
        apply False.elim h47
      case inr h48 =>
        -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
        have h49 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h25
        -- We have shown the premise of h34, we can now drive its conclusion.
        let h50 := h34 h49
        -- False on the left can always be used.
        apply False.elim h50
  case inr h51 =>
    -- Disjunctions on the left can always be decomposed.
    cases h33
    case inl h52 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h53 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h52
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h54 := h34 h53
      -- False on the left can always be used.
      apply False.elim h54
    case inr h55 =>
      -- We want to use the implication h34 based on <expert-advice>. So we show its premise.
      have h56 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h25
      -- We have shown the premise of h34, we can now drive its conclusion.
      let h57 := h34 h56
      -- False on the left can always be used.
      apply False.elim h57



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62831127236936998961891339589 : ((p4 ∧ ((((False ∨ (p2 → p4)) ∨ (p3 ∨ p3)) → p2) ∨ (p4 → (((True → p1) ∨ True) ∨ ((True ∨ (True ∧ p1)) → (p1 ∧ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147974475328414461355052630815 : (((p5 → ((((p4 ∨ p4) ∨ True) ∨ ((((True ∨ p1) ∨ (False ∨ p5)) → False) ∨ p3)) → p3)) ∧ (True → False)) ∨ (((p2 → True) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146981938900222616138120565059 : (((((True ∨ (p5 → p2)) ∨ ((((p3 ∧ False) ∨ p5) ∨ (p4 ∨ ((p1 ∧ p1) ∨ p5))) → p5)) → p5) ∧ p5) ∨ (((p5 ∧ True) ∧ p1) → p1)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137133353337100934453485013549 : ((True ∧ (p4 ∧ ((p5 ∧ False) ∨ ((True → (((False ∨ p3) ∧ p2) ∧ (False ∨ p1))) ∧ (False ∧ ((True ∧ p5) ∨ p4)))))) ∨ (True ∨ (p1 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50357603639874055074026113079 : (((((False ∨ False) → (p1 → False)) → (((p3 ∨ True) → (p2 ∨ p4)) ∨ ((p4 ∨ (p4 ∧ True)) ∨ p4))) ∨ (p1 → (p5 → (p1 ∧ True)))) ∨ p1) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46885167940505111252017803037 : ((((((((True → ((True ∨ ((True → p5) ∧ p2)) ∨ p5)) ∧ (p3 ∧ p5)) ∨ ((False ∨ True) ∧ p2)) ∨ p1) ∨ p3) ∨ p4) ∨ (p3 ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41092050105138071732379357818 : (((((p3 → (True ∧ (((p5 ∨ (p2 → p5)) → ((p2 → p5) → ((p3 → p5) → False))) → p1))) → p1) ∧ ((False → p5) ∨ p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160054245520688815764837813374 : (((False ∧ (p4 ∧ ((True → (p5 → (False ∨ ((False ∨ (p3 → True)) ∧ False)))) ∧ (False ∨ False)))) → p2) → (p2 ∨ ((p3 ∧ (p4 ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345771627327044840212326400503 : (p3 → (((p4 ∨ (((p4 → p1) ∧ (True → False)) ∧ ((p5 ∧ p4) → (((p1 → p5) ∨ p4) ∨ (p3 → ((p5 → p2) ∨ p1)))))) ∧ p1) → p4)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h12 := h10 h11
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116106578669998728756499189775 : ((((p5 ∧ False) → p2) ∧ ((p3 ∨ p3) ∧ ((((((p2 ∨ p2) → True) → p1) ∧ (p5 → ((p5 → True) ∨ p4))) ∨ False) ∨ False))) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3948964765627195437325935766 : (False ∨ (p4 ∨ (((False ∨ ((True ∨ ((p5 ∨ (True ∧ (p5 ∨ p5))) ∨ p2)) ∧ p3)) ∨ False) ∨ (True ∨ ((p4 ∧ (p3 ∧ p5)) ∨ p4))))) := by
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
theorem thm_5_vars_187190565420076640845187756663 : (((True ∨ p2) → (p5 → ((p1 ∧ ((p2 ∧ p3) ∧ p4)) → p2))) → (((p1 → (p1 ∨ (p2 ∧ p5))) ∨ p5) → ((p1 ∧ False) ∨ (p5 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52757960596308834686056271209 : ((((((((p4 ∧ (p1 ∧ True)) ∨ p1) → True) ∨ p4) ∧ (p5 ∨ p3)) → p5) → (((p1 → p2) ∨ ((True ∧ (p1 ∨ False)) ∧ p1)) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616329090406626973397152376644 : ((((((p1 ∧ p2) ∨ (p4 ∨ (((p2 → True) → p2) ∧ (False ∧ p1)))) ∨ ((True → ((((True → p4) ∨ True) ∨ True) ∧ p3)) ∨ p4)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_46935188422769409635424660780 : ((((p1 ∧ (p5 ∧ ((p2 → (p4 ∨ (((p2 → True) ∧ (p3 ∧ p1)) ∧ p1))) ∨ (p1 ∧ ((p1 ∨ p4) ∨ p2))))) ∨ p1) ∨ (p1 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305525726199224689634200996478 : (p1 ∨ (((((p2 → (((False ∨ p2) ∧ p2) ∨ False)) → p3) ∧ p3) ∧ (False → p2)) → ((p1 ∨ ((p1 ∨ ((p2 ∨ False) ∨ p4)) → p4)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54849731393687514624962977761 : ((((((p2 ∧ p2) ∧ p3) ∨ p4) ∧ False) ∧ ((True ∧ ((p5 ∨ (False → (p3 ∧ p2))) ∨ (p2 ∨ (p5 ∧ ((True ∨ p4) → p1))))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316913304480511608928324460166 : (p3 ∨ (p2 → (((((p2 ∨ (p3 → (p1 ∨ ((p5 ∧ True) → (False ∧ p4))))) ∨ (p1 ∨ p4)) ∨ p2) → ((p2 ∧ (p5 ∨ False)) ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173097384158819483335376538682 : ((p1 ∨ (p3 ∧ (((p1 ∨ p3) ∨ ((p3 ∧ (p2 → p4)) → p1)) ∨ (p3 → False)))) ∨ (p4 ∨ (((p3 ∨ (p3 → p5)) ∧ p4) → (True ∨ p1)))) := by
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
  cases h2
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
theorem thm_5_vars_49811256027767730817548137771 : (((p1 → (((((p1 ∧ ((p3 ∨ p5) ∨ p4)) ∨ p2) → (False ∨ (p3 ∨ (False ∧ (p4 ∨ p1))))) → p3) ∨ p2)) → (p5 ∨ (False ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186440007830300604299566807176 : (((p4 → ((True → (False ∧ ((p2 ∨ p1) ∨ p2))) ∨ p4)) → p4) → ((p1 → (p1 → (((False ∧ p2) ∨ p5) ∨ (False ∨ p2)))) ∨ (p4 ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → ((True → (False ∧ ((p2 ∨ p1) ∨ p2))) ∨ p4)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116046977439211014198555867273 : (((False → (p4 ∧ (p3 → p1))) → ((p4 ∨ p4) ∨ ((p4 ∧ (False → (p4 → (p2 → (p4 ∧ (False ∧ (True → p3))))))) ∨ True))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54201538517369207282673598810 : (((((False → (False ∨ False)) → (True → p4)) ∨ p4) ∧ (p2 ∧ ((p3 ∧ ((p1 ∨ (((p2 ∨ p5) → p3) ∨ p5)) ∨ p3)) ∨ (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647066329981341909712109644314 : ((((p3 → ((True → ((p5 → (p1 → ((p3 ∨ False) ∧ p1))) ∨ (p1 ∧ ((p2 → False) ∧ False)))) ∨ ((p4 ∨ p5) ∨ (p1 → p4)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115489967259117595057977193606 : ((((((p3 ∨ p3) ∧ (p2 → p2)) ∧ p1) ∨ p2) → (p4 ∨ (((False ∨ (((p2 ∧ p4) ∧ p5) ∨ (p3 ∨ False))) → p5) ∨ p2))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305801703277996569883669497656 : (p1 ∨ (((((p5 ∧ p1) ∨ False) ∨ p3) ∨ (p2 → p4)) → (((p1 ∨ (p2 ∨ p2)) ∧ (False → p3)) ∨ ((False ∧ (p3 → (True ∧ True))) → False)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h4 =>
        -- Conjunctions on the left can always be decomposed.
        let h5 := h4.left
        let h6 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- False on the left can always be used.
        apply False.elim h8
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- False on the left can always be used.
      apply False.elim h13
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54987374818153544899068364527 : ((((p3 → p3) ∧ (p1 → (p2 → p1))) ∧ ((((True ∨ p5) → (p3 ∨ (p4 ∨ p2))) → ((p2 ∧ (p3 → (p4 ∨ p5))) ∧ p3)) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118639746682339743593687873197 : ((p4 ∨ ((p3 ∧ True) ∨ (p3 → ((((False ∧ p5) ∨ p2) ∨ (((False ∨ p5) ∧ ((p4 ∨ p5) ∧ True)) → p5)) ∨ (p1 → p1))))) ∨ (p2 ∧ p5)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135378338537051798989603881246 : ((((False ∧ (p1 ∧ (True ∨ (((p4 ∨ (p1 ∨ (p2 ∧ (False → True)))) → p5) → False)))) ∨ p2) ∨ ((p2 ∨ False) ∧ True)) ∨ ((p1 ∨ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748505255734669067410638547377 : ((((p3 → True) → ((((True → p5) ∧ ((p4 ∨ (((p4 ∨ (p1 → p2)) ∨ (p4 ∧ (p2 ∨ True))) ∨ p3)) → True)) ∧ (True ∨ p4)) → p5)) ∨ p1) ∧ True) := by
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
  cases h4
  case inl h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h11 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h12 := h5 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64666777643420120479962111174 : ((p1 ∨ (p1 ∨ (((p4 ∨ (p3 → p2)) → True) ∧ (p5 ∧ ((True → p1) ∧ (p2 → ((p2 → False) → ((p1 → (p1 ∧ p1)) → p3)))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151157900465974363317057085298 : ((((((((False ∨ False) ∨ False) ∨ (((p2 ∨ p3) → p5) → p5)) → p2) ∧ p4) → ((False ∧ p3) ∧ False)) → p5) → (((False ∨ p5) ∨ True) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727746505139992754269671951644 : ((((False ∨ (p5 ∧ p4)) ∨ (((((p4 ∧ p2) ∧ p2) ∨ (((p3 ∨ p1) → ((p3 ∨ p5) ∨ True)) ∨ True)) ∧ p2) → ((p3 ∨ p2) ∧ p2))) ∨ p1) ∧ True) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  -- Conjunctions on the left can always be decomposed.
  let h12 := h1.left
  let h13 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h12
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h13
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628545557416050598903066745691 : (((((False ∨ (((((p2 ∨ p5) ∧ p5) ∧ (((p3 ∨ p4) → ((True ∧ (False → p5)) ∧ p4)) ∧ p5)) ∨ (False → p3)) → p1)) ∧ p3) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65084779780319370534002360744 : ((p2 ∨ (False ∨ ((p4 ∨ (((p2 ∨ p5) ∨ p5) ∨ ((True → (False → ((True ∨ p3) → False))) ∨ (p1 ∧ (p4 ∨ p3))))) ∧ (True → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809663152814093853270565561887 : (((p5 → ((p5 → ((False ∨ (p2 ∧ (((False → p5) ∨ ((False → p5) ∧ p2)) ∧ p1))) → ((p3 ∧ p3) → ((p1 ∨ p2) → p1)))) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215746983436240381151539703008 : ((p1 ∨ ((p1 ∧ False) ∧ p2)) ∨ (True → (((p1 → ((p5 → p1) ∨ p1)) → ((p3 → (p3 ∧ True)) → (p4 → True))) ∧ ((p1 ∧ False) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168058525307278564124479515491 : ((((True → (p1 ∧ False)) ∧ p4) ∧ (p5 → (((p5 ∨ p3) ∧ ((True → p2) ∧ p5)) ∧ p3))) → ((False ∧ p4) ∨ (True ∧ ((p2 → p5) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157459472143074172043545776609 : ((((p5 → ((((p3 → False) ∨ (False ∨ p5)) ∧ (p4 ∧ p1)) ∨ (p3 ∧ p1))) ∧ p1) ∨ (p3 ∧ p5)) ∨ (p3 → ((p5 ∧ (p4 ∨ p4)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256931807137634709420240723897 : ((p1 ∨ p4) → (p2 → (((True ∧ ((p5 → (True → True)) ∧ p1)) → ((((p3 → p5) → (False ∧ p1)) ∧ p2) → p4)) ∨ (p1 ∨ (p4 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134096367209353735635995173159 : ((((False ∨ ((p2 → False) ∨ ((p4 ∧ (False ∨ (((p2 → p3) ∨ p1) ∨ ((p4 ∧ p2) ∧ p2)))) ∧ p1))) → False) ∨ p4) ∨ (p2 → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330979295414377915731623392071 : (True → (p5 → (((((True ∨ p5) → (((p4 ∧ p3) ∨ (p2 ∨ (True → p3))) ∨ True)) → ((p3 ∨ p1) ∧ p4)) → p4) ∨ ((p3 ∨ p3) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((True ∨ p5) → (((p4 ∧ p3) ∨ (p2 ∨ (True → p3))) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_760516452646361951317065415372 : (((p2 ∧ (p1 ∧ (p3 → ((((p1 ∨ (p1 → ((True ∨ (p1 → (p5 ∨ (False → p3)))) ∨ p5))) → p1) ∧ (False ∨ (False → p5))) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253775507695887437375719441151 : ((p1 ∧ p1) → (p4 → ((((p1 → (p5 ∧ False)) → (p4 → ((((p3 ∨ p3) ∨ p4) ∨ False) → p2))) → False) → ((p5 ∨ p3) ∧ (False ∧ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h6 : ((p1 → (p5 ∧ False)) → (p4 → ((((p3 ∨ p3) ∨ p4) ∨ False) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h13 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h14 := h7 h13
          -- We need to get the right conjuct of h14 based on <expert-advice>.
          let h15 := h14.right
          -- False on the left can always be used.
          apply False.elim h15
        case inr h16 =>
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h17 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h5
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h18 := h7 h17
          -- We need to get the right conjuct of h18 based on <expert-advice>.
          let h19 := h18.right
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h21 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h22 := h7 h21
        -- We need to get the right conjuct of h22 based on <expert-advice>.
        let h23 := h22.right
        -- False on the left can always be used.
        apply False.elim h23
    case inr h24 =>
      -- False on the left can always be used.
      apply False.elim h24
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h25 := h3 h6
  -- False on the left can always be used.
  apply False.elim h25
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h28 : ((p1 → (p5 ∧ False)) → (p4 → ((((p3 ∨ p3) ∨ p4) ∨ False) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- Disjunctions on the left can always be decomposed.
    cases h31
    case inl h32 =>
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h34 =>
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h35 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h36 := h29 h35
          -- We need to get the right conjuct of h36 based on <expert-advice>.
          let h37 := h36.right
          -- False on the left can always be used.
          apply False.elim h37
        case inr h38 =>
          -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
          have h39 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h27
          -- We have shown the premise of h29, we can now drive its conclusion.
          let h40 := h29 h39
          -- We need to get the right conjuct of h40 based on <expert-advice>.
          let h41 := h40.right
          -- False on the left can always be used.
          apply False.elim h41
      case inr h42 =>
        -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
        have h43 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h27
        -- We have shown the premise of h29, we can now drive its conclusion.
        let h44 := h29 h43
        -- We need to get the right conjuct of h44 based on <expert-advice>.
        let h45 := h44.right
        -- False on the left can always be used.
        apply False.elim h45
    case inr h46 =>
      -- False on the left can always be used.
      apply False.elim h46
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h47 := h3 h28
  -- False on the left can always be used.
  apply False.elim h47
  -- Conjunctions on the left can always be decomposed.
  let h48 := h1.left
  let h49 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h50 : ((p1 → (p5 ∧ False)) → (p4 → ((((p3 ∨ p3) ∨ p4) ∨ False) → p2))) := by
    -- Implications on the right can always be decomposed.
    intro h51
    -- Implications on the right can always be decomposed.
    intro h52
    -- Implications on the right can always be decomposed.
    intro h53
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h55
        case inl h56 =>
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h57 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h58 := h51 h57
          -- We need to get the right conjuct of h58 based on <expert-advice>.
          let h59 := h58.right
          -- False on the left can always be used.
          apply False.elim h59
        case inr h60 =>
          -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
          have h61 : p1 := by
            -- One of the premise coincides with the conclusion.
            exact h49
          -- We have shown the premise of h51, we can now drive its conclusion.
          let h62 := h51 h61
          -- We need to get the right conjuct of h62 based on <expert-advice>.
          let h63 := h62.right
          -- False on the left can always be used.
          apply False.elim h63
      case inr h64 =>
        -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
        have h65 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h49
        -- We have shown the premise of h51, we can now drive its conclusion.
        let h66 := h51 h65
        -- We need to get the right conjuct of h66 based on <expert-advice>.
        let h67 := h66.right
        -- False on the left can always be used.
        apply False.elim h67
    case inr h68 =>
      -- False on the left can always be used.
      apply False.elim h68
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h69 := h3 h50
  -- False on the left can always be used.
  apply False.elim h69



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59393227568248798107111754309 : (((True → p1) ∨ (False ∧ ((((((False ∧ False) → ((p3 ∨ (p5 ∧ p1)) ∧ p2)) → (p3 ∧ (False ∨ p4))) → (p2 ∨ False)) ∧ False) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184096240073137980898130541016 : ((((True ∧ (p4 ∨ p3)) → (p1 ∧ ((p2 ∨ True) ∧ False))) ∨ p1) ∨ ((p1 ∧ p3) → (((p3 ∨ False) ∧ p5) ∨ ((p4 ∨ p1) ∧ (p5 ∨ p1))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116872340546008559121680477526 : (((p2 → p1) ∨ (p5 ∨ (((p3 ∧ (((((p1 ∨ (p2 ∨ p4)) ∧ p1) ∨ p4) → ((p3 → p2) → False)) ∨ p2)) → p4) → p2))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158591512643635440627768384189 : ((False ∧ ((((((((p4 → p2) ∨ (p4 ∧ (p3 ∨ False))) ∨ p3) → p1) ∨ False) ∨ p5) ∨ p5) ∧ False)) ∨ ((p5 ∨ False) → (p1 ∨ (p5 → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161186391959555971260574130739 : (((p2 ∨ False) ∨ ((p1 → p3) → (p5 ∧ ((False ∧ ((p3 → p5) ∧ ((True ∨ p5) ∧ p5))) → p4)))) → ((((p1 → False) ∨ p3) → p1) ∨ True)) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113886513709486887787541117124 : (((((((p1 ∨ (False ∨ ((p5 ∨ p3) → True))) ∧ (True ∨ False)) ∧ (p4 ∨ p1)) ∨ (True ∧ True)) ∨ p4) ∧ ((p4 ∨ p1) ∨ True)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165773628844361444058747443374 : ((((p5 ∨ (p5 ∧ True)) → p5) → ((p2 ∨ (p2 ∨ (p4 ∨ (p4 ∧ False)))) ∨ (p3 → True))) ∨ ((p3 ∧ (((p1 ∧ p3) → p4) → p2)) ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136157526834456006411183719689 : (((p3 ∧ ((p2 ∨ (False → (p1 ∨ p4))) ∨ p3)) → ((p5 → (((p4 ∨ (p1 ∧ (False → False))) → True) → p3)) → p5)) ∨ ((False ∧ p1) → p5)) := by
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
theorem thm_5_vars_164605950198554854493119325507 : (((False ∧ (((p5 ∧ False) ∨ p4) ∨ (p5 ∨ (p2 ∨ ((True ∨ (p3 ∧ p1)) ∧ p5))))) ∧ True) ∨ (((p3 ∨ ((p3 → p2) ∧ p5)) ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313991145605457058261597149339 : (p3 ∨ ((((p4 ∨ p1) ∨ False) ∨ ((False ∨ p3) → (False ∨ ((((False → True) ∨ (((p5 → True) → False) ∧ p1)) → p3) → p3)))) ∨ (True ∧ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177829175617761234479800659479 : (((p5 → (p1 → (p4 ∨ (((p2 ∧ p3) ∨ (p1 ∨ p4)) ∧ p2)))) ∧ p4) ∨ (False → ((p3 ∧ (p1 ∨ (p1 ∨ (p2 ∧ p1)))) → (p1 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h1
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h1
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620947856979566979407754475728 : (((((p4 ∨ p4) → ((p1 ∨ (True ∧ ((p5 → (p3 ∧ True)) → (((True → p3) ∨ p5) ∨ p1)))) → (((p3 → p5) ∨ False) ∨ p1))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715673289106752141214440383720 : (((((p4 → (p3 → p4)) ∧ p2) ∧ ((True ∧ (((p4 ∧ p1) ∨ p2) ∧ (p5 → (((True → ((p1 → p1) → p4)) ∨ p3) ∨ p3)))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339809990657417395468059873229 : (p1 → (p5 ∨ (((True ∨ True) → (((p3 ∧ p3) → p3) ∧ p2)) ∨ (((p3 ∧ (False → True)) ∧ (False ∨ p1)) ∨ (p4 ∨ ((p5 ∧ p5) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261159554952243361931589975177 : ((p4 → p4) → ((p5 ∨ ((True → (p1 ∧ p4)) → True)) → ((p2 → ((p5 ∨ (p1 ∨ ((((p2 ∧ False) ∨ p1) → p3) ∧ p4))) ∨ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50098192444018587638838914153 : (((p4 ∧ ((((True ∨ True) → p2) ∧ (((p4 → p4) ∨ p1) ∧ ((p3 → (True ∨ p5)) → p4))) ∨ p4)) ∧ (((p5 → False) ∨ p4) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348185349520959020365906286085 : (p3 → ((p4 ∨ p1) → ((p4 → ((p4 → (p4 ∧ (((p5 → (p2 ∧ p5)) → ((True ∧ (p1 ∧ (p2 ∧ p5))) ∧ True)) → p5))) ∨ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_129425960477186295657514781211 : (((p4 ∨ (p1 → ((True ∧ p2) ∨ (p5 → (p2 → (((((False → p2) ∧ p5) ∨ p3) → p4) ∨ (p4 ∨ p2))))))) ∨ p4) ∧ ((False → p1) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50441897459655235196227320189 : (((False ∨ (p5 ∨ (((p3 → ((p2 → (p5 ∨ True)) → p5)) ∧ (False ∨ p2)) → (p3 ∧ (p3 ∨ p1))))) ∨ ((p5 ∧ (p2 ∨ p5)) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_429888868470282736053097401633 : (((((True ∧ ((p2 ∧ (p4 ∧ (p4 ∨ (True → p1)))) ∨ p5)) ∧ (((p1 → (True ∨ (p4 ∨ p2))) → (p1 ∨ p1)) → p4)) ∨ (True ∨ False)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_205249206862132514165060117099 : ((((p5 ∨ p1) ∨ p3) ∨ (p2 ∨ p2)) ∨ (p4 ∨ (True ∧ (True ∨ (p4 ∨ ((((False → (p5 ∨ (p4 → (p1 ∨ False)))) ∧ True) ∨ p2) ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66245707999810794211162038549 : ((p5 ∨ ((((False ∧ (True ∧ p1)) → False) → p2) → ((((((False ∧ p2) ∨ p3) → p5) ∨ p3) → ((p1 ∧ p3) ∨ (p2 ∧ False))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632517281718491655968616001798 : (((((p4 ∨ ((p5 → p1) ∧ ((((p1 ∨ (p2 ∧ ((True → False) → ((True ∧ True) → (True → True))))) → p5) ∨ False) ∧ p2))) → p5) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717068774318860227560179751189 : ((((True ∨ ((p4 → True) ∨ p1)) ∧ (((True → True) → ((((False → False) → p3) ∨ ((True → p3) → (p4 ∧ p4))) → (False ∧ True))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149829852457233776713225480357 : ((p1 ∨ ((p2 → (((p3 ∨ (True → True)) ∨ ((p1 ∨ (p3 → p1)) → p5)) ∧ p3)) ∧ (p2 ∧ (p2 → True)))) ∨ (p2 → (p3 ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714944361424203771507182536840 : ((((True ∨ (((p4 ∧ p3) ∧ p2) ∨ p3)) → ((((p5 ∧ p5) ∧ p4) ∨ True) → (((p5 ∨ ((p3 ∧ True) ∧ (p1 ∧ p1))) ∨ p2) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_798365096137843098952931863285 : (((p1 → ((((p1 → (p1 ∧ ((p2 → p4) ∧ (p1 ∨ p1)))) ∨ p5) → p2) ∧ (((p5 ∨ p2) ∨ True) ∨ (p3 ∧ (False → (False ∧ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161489393119880043662114015869 : ((p4 ∧ ((((p2 ∨ ((p3 → (False → True)) ∨ True)) ∨ p3) ∧ ((p5 ∨ p1) → (p1 ∧ p4))) ∧ p5)) → ((((p2 ∧ True) → p3) ∨ p1) ∧ p5)) := by
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
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : (p5 ∨ p1) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- We need to get the left conjuct of h11 based on <expert-advice>.
      let h12 := h11.left
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : (p5 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h16 := h7 h15
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h19 : (p5 ∨ p1) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h20 := h7 h19
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h21
  case inr h22 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h23
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- One of the premise coincides with the conclusion.
    exact h22
  -- Conjunctions on the left can always be decomposed.
  let h26 := h1.left
  let h27 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h28 := h27.left
  let h29 := h27.right
  -- Conjunctions on the left can always be decomposed.
  let h30 := h28.left
  let h31 := h28.right
  -- Disjunctions on the left can always be decomposed.
  cases h30
  case inl h32 =>
    -- Disjunctions on the left can always be decomposed.
    cases h32
    case inl h33 =>
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- One of the premise coincides with the conclusion.
        exact h29
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h29
  case inr h37 =>
    -- One of the premise coincides with the conclusion.
    exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69019335714758749196354538753 : ((p5 → ((p1 → (p2 ∨ (p4 ∨ ((p3 ∨ ((True ∨ p5) ∧ p3)) ∧ ((p4 ∨ p2) → (((True ∨ False) ∨ (p2 ∨ p4)) ∨ p1)))))) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299333528742149014648082387350 : (False ∨ ((((True ∨ (p2 → p2)) → p4) → (p4 → ((p5 → (p1 ∨ (((p2 ∧ p3) ∧ ((p5 ∧ False) ∧ (p3 ∧ p5))) → p1))) → p2))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49331573984864154624109968065 : (((p5 ∨ ((((p2 ∨ p2) ∧ True) ∧ (False ∨ (p2 → ((p1 → True) ∨ p2)))) ∧ (True ∧ (True ∧ (p1 ∧ True))))) ∨ (p2 ∧ (p2 ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149986645861602077217717130853 : ((p4 ∨ (False ∧ (p3 ∨ ((True ∧ (True ∧ (((p5 ∨ (p1 ∧ True)) ∧ (p5 → p4)) ∨ p3))) → (p4 ∧ p3))))) ∨ ((False ∧ p4) → (p5 ∧ False))) := by
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
theorem thm_5_vars_200985257802513005643147646275 : ((p3 ∨ ((((p5 → p4) ∨ False) ∧ p2) ∨ False)) → (p4 ∨ ((p2 ∧ (((p1 ∨ (p1 ∨ (False → p2))) ∨ p4) → False)) → (False ∨ (False ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((p1 ∨ (p1 ∨ (False → p2))) ∨ p4) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
        have h17 : ((p1 ∨ (p1 ∨ (False → p2))) ∨ p4) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h18
          -- False on the left can always be used.
          apply False.elim h18
        -- We have shown the premise of h16, we can now drive its conclusion.
        let h19 := h16 h17
        -- False on the left can always be used.
        apply False.elim h19
      case inr h20 =>
        -- False on the left can always be used.
        apply False.elim h20
    case inr h21 =>
      -- False on the left can always be used.
      apply False.elim h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615662251063614474969474919869 : (((((((p3 ∨ p3) ∧ ((((p2 ∨ False) ∨ p5) ∧ (False → p4)) ∨ False)) → p4) ∧ ((((True ∨ (p1 ∨ p3)) → p3) ∧ False) ∧ True)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255035362897002815144986967458 : ((p4 ∧ p1) → (True ∧ ((p2 ∨ ((((False ∧ (p5 → p1)) ∨ (False → True)) ∧ (p2 ∧ (p2 ∨ (p2 → (p4 ∨ p3))))) ∧ (True ∧ False))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



