variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134937330395331830611126295151 : ((((((False ∨ ((p5 ∧ (p3 ∨ ((False ∧ True) → p2))) → False)) → p2) → (True ∧ False)) ∧ (p1 ∧ p5)) ∧ (True → p1)) ∨ (False → (p5 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315396953953611238941577379031 : (p3 ∨ (((p5 → False) ∧ p1) ∨ ((((p1 ∧ (p2 → (((True → p1) → True) → (p3 ∧ (True ∧ (p1 ∧ (p5 ∨ True))))))) ∨ True) ∨ True) ∨ p3))) := by
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
theorem thm_5_vars_180547824503244330211375033336 : (((False ∨ ((True ∨ ((p2 → False) → p4)) → p1)) ∨ ((p1 ∧ p4) ∨ p5)) → ((False ∨ (((p1 ∨ False) ∨ ((p4 → p2) → p5)) → p3)) → p3)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h8 : ((p1 ∨ False) ∨ ((p4 → p2) → p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
          have h9 : (True ∨ ((p2 → False) → p4)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h7, we can now drive its conclusion.
          let h10 := h7 h9
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h11 := h4 h8
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : ((p1 ∨ False) ∨ ((p4 → p2) → p5)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : ((p1 ∨ False) ∨ ((p4 → p2) → p5)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h20
          -- One of the premise coincides with the conclusion.
          exact h18
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h19
        -- One of the premise coincides with the conclusion.
        exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62864076973292065731534480129 : ((p4 ∧ ((False ∧ (p1 ∧ p1)) ∧ (((False → (((p5 ∨ ((((p4 ∨ p5) → (True ∨ p2)) ∨ True) ∨ p4)) ∧ p5) ∧ p5)) ∧ p2) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180362132761016017992478128649 : ((((p4 ∨ (((p4 → False) ∨ True) ∧ (True ∧ p3))) ∨ p1) ∨ (p1 ∨ p2)) → (p3 ∨ (((False → p5) → (((True → p3) ∧ p4) → p3)) ∨ True))) := by
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
        -- Conjunctions on the left can always be decomposed.
        let h6 := h5.left
        let h7 := h5.right
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h7.left
          let h10 := h7.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h10
        case inr h11 =>
          -- Conjunctions on the left can always be decomposed.
          let h12 := h7.left
          let h13 := h7.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345574590335399104976179176528 : (p3 → ((((p1 ∨ p1) ∨ p5) ∨ ((p5 ∨ p5) ∨ (p3 ∧ (p1 ∧ (((True ∧ (p3 → p5)) ∨ (p4 → ((p1 ∨ True) ∧ p3))) ∨ True))))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55612012993492610408273904965 : (((p1 → (True → ((True ∨ p2) → True))) → (((p5 ∨ p2) ∨ ((p3 ∧ p1) ∨ p1)) ∧ (False ∨ ((p5 ∧ (p3 ∧ True)) ∧ (p2 ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164715721023757035271235026575 : ((((((p3 ∨ ((True ∧ p4) ∧ p2)) → ((p1 ∨ (False ∨ p2)) → p5)) ∨ True) → p4) ∨ False) ∨ ((p4 → False) → ((False → (False ∧ p5)) ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165681034773546241748408194424 : (((((False ∨ True) ∨ (p3 ∨ True)) → p3) → ((p4 ∨ p3) → ((p3 ∧ p3) → (p3 ∧ p4)))) ∨ (((p4 ∨ p5) ∧ p2) ∨ ((p1 → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_221143017551617771050603329541 : (((True ∨ p4) ∨ p1) ∧ ((((p3 → (((p2 ∨ ((True ∧ (p3 ∨ (p3 → p5))) ∨ p1)) ∧ p1) ∨ p2)) → (p1 → False)) ∨ (p3 ∨ True)) ∨ p2)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_933066197903496904417921125550 : ((((True → ((p2 ∧ p3) ∧ (True ∧ (p5 ∧ p4)))) ∧ (((((False ∧ p4) ∧ ((p4 → p1) ∨ p5)) ∧ p5) ∨ (p5 ∧ (False → p4))) → p4)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218093066783333526982576970141 : (((True → p5) ∧ (p2 → True)) → (p1 → (((((p2 ∨ (p3 ∧ p4)) ∧ p1) → p2) ∨ p3) → (False ∨ (False ∨ (p4 → (p4 ∧ (p3 ∨ p4)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h1.left
    let h6 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h1.left
    let h10 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322571284321754172209041719441 : (p5 ∨ ((p4 ∨ ((False ∨ ((((p1 ∧ ((p2 ∧ p3) ∨ p2)) → (False → p3)) ∧ (p3 ∧ (p3 → ((True ∧ p2) ∧ p4)))) ∨ p4)) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779744705538199333878898054095 : (((p2 ∨ (((((p2 ∨ (((p5 ∧ False) → p5) → p1)) ∨ (p4 ∨ True)) → (p5 → (p1 → p2))) ∧ (p3 ∨ ((True ∨ p5) → False))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231430100943715174458312164075 : (((p2 → True) ∨ p4) → (((False ∨ (((False → (False ∧ (p5 → (False → p5)))) ∨ ((p5 → (p4 ∨ True)) → (p5 ∨ p3))) → p5)) ∨ p4) ∨ True)) := by
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
theorem thm_5_vars_62731567274201097381239210822 : ((p4 ∧ ((True ∧ (((((((p2 ∨ p4) ∨ p2) ∨ (p3 → p1)) ∧ True) → (p1 ∨ (True → p4))) → p4) ∨ (False ∨ p2))) ∧ (False ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615831437018143691146642217391 : ((((((((p2 → p3) ∧ p2) ∧ ((p5 ∨ p2) ∨ (p1 ∧ p2))) ∨ (p5 ∨ True)) ∨ (p2 ∧ (((p1 ∨ (True ∧ p1)) ∨ p5) ∧ True))) ∨ p4) ∨ p3) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555817302662587446757842916322 : (((p3 ∨ ((((((p5 ∧ p4) → p2) → False) ∧ ((p1 ∨ ((((p2 ∧ p5) → (True → p1)) ∧ (p2 ∧ True)) ∧ p4)) ∧ p1)) ∧ True) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_734356783813354574305387304 : (((((p2 ∨ p1) ∨ p3) → p2) ∨ ((((p3 ∨ p1) → p1) ∨ (p3 → p4)) → (((((p2 ∧ p3) ∧ p5) ∨ True) ∨ False) ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60151822688075617435970802853 : (((p4 ∨ p3) → ((p3 → (p2 ∧ True)) → ((((p5 ∧ True) ∧ (((p1 → ((True ∨ p4) ∧ p4)) → p2) ∨ p5)) ∨ p1) ∨ (p5 → False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42564076176999733143948723757 : (((p1 ∨ (p5 → (((((p1 → ((p1 ∨ p1) → p4)) ∧ (p3 → p2)) → (False ∨ ((p4 → False) ∨ True))) ∨ p3) ∧ (False → p2)))) ∨ False) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190751231242835359521435758791 : (((p3 ∨ (p4 ∨ (p2 → (p3 ∧ p1)))) ∧ (False ∧ p4)) ∨ ((p2 → p5) ∨ (p3 ∨ ((p1 → (p5 → True)) ∨ ((p3 → p4) → (False ∨ False)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687912884946329968427588867886 : ((((((((p5 ∧ p4) ∨ p5) ∧ (False → False)) ∧ p2) ∧ (p2 ∧ (p5 ∧ (p2 → p4)))) ∧ (p5 ∨ ((p2 ∨ ((True → p2) → False)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115882694421142699617898568606 : (((((p5 ∧ True) ∧ p2) ∨ p5) ∨ (((p2 → ((False → p5) → (True → (p1 ∨ p5)))) ∨ ((False ∨ p4) → (p1 ∨ True))) ∨ p3)) ∨ (p4 ∧ p4)) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209516295221570203627039123949 : ((p4 → (((p5 ∧ p1) ∨ p3) → p3)) → ((p3 ∧ p2) ∨ ((((True ∧ p5) ∧ (False ∨ True)) → p3) ∨ (p5 → (p1 ∨ ((p5 ∨ p2) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_672984840466904981811195075137 : (((((((p3 ∧ (((((p2 ∧ True) ∨ p3) ∨ p1) ∨ True) ∨ p5)) ∧ p1) ∨ p1) ∨ (p1 ∨ (True ∨ (True ∧ False)))) → (False ∧ (p3 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_718169140010918614688517602671 : (((((p5 ∧ (p5 ∧ p2)) ∨ p5) ∨ (((((((True ∨ True) ∧ (p1 → p5)) → p2) → p5) → p3) → (p4 ∧ (p3 ∨ (True → p5)))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120995013549401511867515084328 : ((((True → p5) ∧ (False → ((p2 → p3) → (False → (((((False ∨ p5) ∨ p3) ∨ (p5 ∨ p2)) ∨ (True ∨ p3)) ∧ p5))))) ∨ p2) → (p5 → p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62565421210567189245464263109 : ((p3 ∧ (p5 ∨ (p3 ∨ ((True ∧ (((False → p5) → ((p4 ∨ (p5 ∧ False)) ∧ (True ∧ ((p5 ∨ p5) ∧ (p4 → p4))))) ∧ p3)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315137022884590188876719919479 : (p3 ∨ ((p4 ∨ ((p3 ∧ (p1 ∧ p3)) ∧ p4)) ∨ ((True ∨ p2) ∨ (((p5 ∧ (((p2 → (p5 ∧ p2)) ∧ (p1 ∨ True)) → False)) ∧ p2) ∧ True)))) := by
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
theorem thm_5_vars_163344957210405501053285085948 : (((p4 → ((p5 ∧ p3) → (p5 ∨ p5))) → (((p2 → p3) ∨ (p3 → p4)) ∨ (p1 → True))) ∧ ((p5 ∨ p2) → ((True ∧ True) ∧ (False → p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174029165480037452422771411494 : (((p1 ∨ ((p2 ∧ (((p1 → (p3 → (p3 ∧ False))) ∨ False) ∨ p4)) ∨ True)) → p1) → ((p4 ∧ (False → True)) → ((p2 → (True ∨ p1)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : (p1 ∨ ((p2 ∧ (((p1 → (p3 → (p3 ∧ False))) ∨ False) ∨ p4)) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937262592610622633591905280948 : ((((((p4 ∨ p1) ∨ True) → (True ∨ False)) ∧ (((False ∨ ((((p2 → p3) → p3) ∨ False) ∨ True)) ∨ p2) → ((p2 → True) ∧ (True ∧ False)))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((((p2 → p3) → p3) ∨ False) ∨ True)) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313117243733177421059048921205 : (p3 ∨ (((((p3 ∨ p2) → ((p3 → p1) → False)) → (p1 ∧ (True ∨ ((p2 ∨ True) ∨ ((p1 ∧ True) → False))))) → ((p1 ∧ False) ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320362690119647116085340307673 : (p4 ∨ ((p3 → p1) ∨ (((p3 ∧ (True ∧ (p3 ∨ p5))) → ((((p3 ∨ False) ∧ True) → p4) ∨ ((False ∧ (p1 ∨ (p1 → False))) ∨ True))) ∨ p1))) := by
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
theorem thm_5_vars_47986183310050863342288308100 : ((((p1 ∨ ((True ∧ (p1 ∧ ((((p5 ∧ (True ∧ p3)) → p2) → True) ∧ p5))) → p3)) → ((p4 ∧ p5) ∨ (p3 → False))) → (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351543604402241716363621074287 : (p4 → ((p2 ∧ (False → ((((((p4 ∨ p3) ∧ p5) ∧ p4) ∧ p2) ∨ ((p1 → p5) ∨ p4)) ∨ p3))) ∨ (((p1 ∨ p5) ∧ (p1 ∧ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50202824136315956677160110057 : (((((p5 → ((((p3 → (p1 ∨ p4)) ∧ (True → p3)) ∨ (p2 ∨ (False ∧ p2))) ∧ p1)) ∧ p5) ∨ True) ∨ ((p2 → (p3 ∨ p5)) ∨ p2)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347298643697103800865417547930 : (p3 → ((p5 ∨ (p4 ∨ (((p2 → (True ∧ False)) ∧ False) ∧ True))) ∨ (p1 ∨ ((True → False) → ((((p4 → p5) ∧ (p2 ∧ p3)) ∨ p4) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684124840388872885788781216879 : (((((p4 ∧ (((False → ((p2 → (p4 ∧ p4)) ∨ p5)) ∨ (p2 ∧ p2)) ∧ True)) ∧ (p3 ∧ p2)) ∨ (((p2 → p4) ∨ (p1 ∨ p2)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193065099611565168781937560438 : (((((p4 → p2) ∧ p5) ∨ p2) ∧ (p3 → (p1 ∧ p3))) → (((True → p1) ∧ (p1 ∧ p3)) ∨ (p5 ∨ (p2 ∨ (p3 ∨ (p5 ∨ (p2 ∧ True))))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41216792193759193769700432435 : ((((((False ∨ ((p5 → (((p3 ∧ (p4 ∨ (False ∨ True))) ∧ p3) ∧ True)) ∨ False)) ∧ p3) → False) ∧ (True ∨ ((p5 → p1) → p5))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60710258044728634662411184784 : ((True ∧ ((p3 ∧ ((False ∨ p4) ∧ (True ∧ (p3 ∨ p2)))) → ((p1 ∧ ((p3 → p4) ∨ p2)) ∨ (p4 → (False ∨ (p2 → (p1 ∨ p4))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h5.left
    let h9 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341696724537289317869733655780 : (p2 → ((((p5 → (((p1 ∧ ((p5 ∧ p4) ∨ (p5 ∨ ((p5 ∧ False) ∧ True)))) ∧ p5) ∨ (True → p2))) ∨ True) → (p4 → False)) ∨ (p1 ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613919214896998840119693697091 : (((((((False ∧ p5) ∧ (False ∧ (((((p2 ∧ (p3 ∧ p1)) ∨ p5) ∨ False) ∧ p5) → p3))) ∧ (p2 ∧ p2)) ∨ (True ∨ (p3 ∨ p2))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685890701683047288506113394464 : (((((p2 ∨ (True ∧ (False ∧ ((((False ∧ (p4 ∨ p1)) → p4) → (False ∨ p3)) ∧ p4)))) → p3) → ((False ∨ False) ∨ ((True ∧ True) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39606014375283472071535253002 : (((p2 ∨ (((p4 ∧ ((p3 ∧ (p5 → (p2 ∨ (p2 → p4)))) ∧ p1)) ∧ (p5 ∧ p4)) ∧ (((p1 ∨ p5) → True) ∧ (False ∨ p3)))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227949406696058315575927394477 : ((p3 ∧ (p3 ∧ p4)) ∨ (((p1 ∧ (((p2 ∨ p3) ∨ (p3 ∨ p1)) → (((p3 → p5) ∨ True) ∨ (p5 ∧ p3)))) ∨ (p4 ∨ (False → p3))) ∨ p2)) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299391387265119653181366399480 : (False ∨ ((True ∧ (((p2 → (p4 ∧ False)) → p4) ∨ (False ∨ ((p1 → p2) ∨ (p2 ∧ ((((p1 ∨ p2) ∨ p4) ∧ p2) → (p4 ∧ p2))))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260719367052086552067157583997 : ((p3 → p4) → (((p5 ∧ (p5 ∨ p1)) ∨ (((p1 → (False ∨ p5)) → (p5 → (((True ∨ True) → (p3 ∧ True)) ∨ p4))) ∨ p2)) ∨ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57278518820091928563883934481 : ((((p5 ∨ p2) → p5) ∨ ((((((p1 ∨ p5) ∨ (p1 → p1)) ∨ (p4 → p5)) → p1) ∧ p1) ∨ (False → (False ∨ ((p5 ∧ p5) ∧ p2))))) ∨ p1) := by
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
theorem thm_5_vars_39322381421820451193169330953 : (((p2 ∧ ((((((p3 ∨ True) ∧ (p4 ∨ p3)) → True) ∧ p2) ∨ (p3 ∨ ((True ∨ (p3 → ((p5 ∧ p5) → p2))) ∧ p4))) → p2)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112255231556548423101903676681 : (((p4 ∨ (((p1 ∨ p2) → (False ∧ (((True ∧ p3) → p1) → p4))) ∨ (((p3 ∧ p1) → (p4 ∨ p2)) ∧ (p2 ∨ False)))) ∨ True) ∨ (True ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252022856978619539298950419879 : ((p4 → p1) ∨ ((((p5 → ((True ∨ ((((p5 → True) → (p4 → (p3 → p5))) ∨ p2) ∨ p1)) → p2)) ∨ (p3 ∨ True)) ∧ (p2 ∨ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38616149937179501801464706489 : ((((p4 ∨ (p2 ∧ (p4 ∧ (p2 → (p2 ∨ p2))))) ∧ (p2 → (p5 ∨ (p3 → (p1 ∧ (False → (((True → p1) ∨ p5) → p4))))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800315216997188248863533111897 : (((p2 → (((((False ∨ p1) ∨ (((p3 ∨ (p2 ∨ p1)) ∧ p3) ∧ p4)) → False) ∧ ((p4 ∧ p1) ∨ (((p1 ∧ False) ∨ False) ∨ p5))) ∨ p2)) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304700229977136990303089064107 : (p1 ∨ (((((False ∧ ((p4 → (p2 ∧ False)) → p1)) ∨ p4) → ((p4 → (True → p3)) ∨ (((p5 ∧ p2) → p4) ∨ p1))) → p5) ∨ (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151871275086719626275013077209 : (((p4 ∨ (p5 ∨ (((p1 ∨ False) ∧ (p4 ∨ False)) ∨ ((p5 ∧ p5) ∨ True)))) ∨ (((True → p5) ∧ False) → p5)) → (((True ∧ True) ∧ False) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h8
          case inl h10 =>
            -- Disjunctions on the left can always be decomposed.
            cases h9
            case inl h11 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- True on the right can always be proven directly.
              apply True.intro
            case inr h12 =>
              -- False on the left can always be used.
              apply False.elim h12
          case inr h13 =>
            -- False on the left can always be used.
            apply False.elim h13
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Conjunctions on the left can always be decomposed.
            let h16 := h15.left
            let h17 := h15.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h18 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2545461280382827954776080688 : (((False ∧ (p2 → ((p4 ∧ p3) ∨ p5))) ∨ p3) ∨ (((True ∧ (((True → (p3 → p5)) ∧ p2) → p3)) ∧ (p4 ∧ False)) → (p4 ∨ p4))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734495432153787090289576240909 : ((((p1 ∨ False) ∧ ((((((True ∨ p2) ∨ p5) ∨ ((p3 → p5) ∧ (p1 ∨ (True ∨ False)))) ∧ True) → (False ∧ (p2 ∨ False))) ∧ (False ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346386711120695575360379419320 : (p3 → ((p5 ∨ (p1 ∨ ((p5 ∨ (p2 → True)) → (((p5 ∨ ((((p3 ∨ p3) ∨ p2) ∧ p1) ∧ (p5 ∨ p3))) ∧ p3) ∨ p4)))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198708561436235052587382079351 : ((p5 ∨ ((p1 ∨ ((p5 → False) → p5)) ∨ p5)) ∨ (p2 ∨ (((((False ∧ (p2 ∨ (p1 ∧ True))) → ((p4 ∨ True) ∧ p4)) ∧ False) ∧ True) → p2))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658681226548523427913036348185 : ((((p4 ∨ (((p5 ∨ False) → (True → (((p5 ∨ (True ∨ p1)) ∧ (((False ∧ p5) ∧ p4) ∧ p4)) ∨ True))) → (p1 ∨ p2))) ∨ (p3 → p3)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_50844820658991940935753017276 : ((((p3 ∨ (p3 ∨ (p5 → ((False ∨ p4) → (p5 ∨ (p5 ∧ ((True ∧ p5) → p5))))))) ∧ p5) ∧ ((p2 → p2) → (p5 ∧ (True ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40599246940855666767418731711 : (((((((((True ∨ (p2 ∧ p1)) ∨ ((p5 ∨ p1) → p1)) ∧ (p5 ∨ ((p1 ∧ p3) ∨ p4))) ∨ (p4 ∧ p2)) ∧ True) ∨ p3) → p2) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111624295787621041780312855512 : ((((((((p2 → ((p1 ∨ (p3 ∨ True)) → p1)) ∨ (p2 ∧ p1)) → p1) ∨ (p1 → (p5 → p3))) ∨ (True ∨ p1)) ∨ p5) ∨ p1) ∨ (False ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_166572940545075341055537296088 : ((True → (((p4 ∧ (True → (p2 → p4))) ∨ ((((p2 → True) ∧ p2) ∧ False) ∧ p5)) ∨ p2)) ∨ ((False ∧ (p4 ∧ (p2 → p1))) → (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_11490624831803066071883866301 : (((((p2 → ((False → ((True ∧ (p2 → p3)) ∧ (((True → (p4 → p2)) ∧ p3) → p5))) → p5)) → (p5 → p3)) ∧ (p5 ∧ p5)) → p3) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → ((False → ((True ∧ (p2 → p3)) ∧ (((True → (p4 → p2)) ∧ p3) → p5))) → p5)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h6
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- One of the premise coincides with the conclusion.
  exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314545761098555463567324198462 : (p3 ∨ (((p2 ∧ (((True → p3) ∧ (True ∧ (True → p3))) ∨ (True ∨ p2))) ∨ ((p5 ∧ p3) ∨ True)) ∨ (((False ∨ p3) → (p4 → p5)) ∨ False))) := by
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
theorem thm_5_vars_166703704306515538308436615281 : ((p3 → ((False ∨ (((p5 ∧ p3) → ((p3 → p4) ∨ (p2 ∨ p4))) → (p4 ∨ p1))) ∨ p3)) ∨ (((p3 ∧ True) ∧ p1) → (p2 → (False → p4)))) := by
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
theorem thm_5_vars_676891384404744294717430531018 : ((((p4 ∨ (p3 ∨ (True → ((p4 ∨ (p1 → (False → ((True → True) ∨ p5)))) ∨ (p1 ∨ (p1 ∨ p1)))))) ∧ ((p4 ∧ p4) ∧ (True ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801026820650477732521726581492 : (((p2 → (((((((((True ∨ p5) → True) → p2) ∨ (p4 ∧ p4)) → True) ∨ (p5 → p5)) → p4) ∨ (p3 ∧ p5)) ∨ (False → (p3 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315669506689658711391613444911 : (p3 ∨ ((p4 ∧ p4) ∨ (False ∨ (p3 ∨ (((((p3 → (((((p5 ∧ True) → False) ∨ p4) → False) ∨ p1)) ∧ False) ∧ p5) → p4) ∨ (False → p4)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116117224042495763526260465511 : ((((p1 → p2) → p1) ∧ ((((p5 ∧ True) ∧ p5) → (((True → (((p5 ∨ p2) ∧ p3) → p4)) ∧ p2) ∨ (p4 ∧ p1))) ∧ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114045928706687633922116570677 : ((((((p4 → ((p4 ∧ p1) → p4)) ∧ (((p1 ∨ p1) ∨ p1) ∨ (False → p2))) ∨ True) → (p1 → p2)) ∨ ((False → p4) ∨ p5)) ∨ (p4 ∨ p5)) := by
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
theorem thm_5_vars_133556034011534789531612561981 : (((((((p4 ∨ p5) ∧ p5) ∨ ((p5 ∧ p1) ∨ (((False ∧ (True ∧ True)) ∨ (p1 ∧ p1)) → p2))) ∧ p1) ∨ False) ∧ p5) ∨ ((p4 ∧ False) → False)) := by
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
theorem thm_5_vars_186674606559684295677396125731 : ((((p3 → p4) → (p5 → (p1 ∧ p4))) ∧ (p4 ∨ (p3 ∨ p5))) → (p1 ∨ ((((((p5 ∨ False) → p4) ∧ p3) ∨ (True ∧ p1)) ∧ False) → p5))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h7
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h18
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- False on the left can always be used.
        apply False.elim h18
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h26.left
      let h28 := h26.right
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- False on the left can always be used.
        apply False.elim h28
      case inr h32 =>
        -- Conjunctions on the left can always be decomposed.
        let h33 := h32.left
        let h34 := h32.right
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773258118529937400946360317501 : (((False ∨ ((((False → (p4 → (p3 ∨ (p2 ∧ (True ∨ p4))))) ∨ (True ∧ p5)) ∧ (((False ∨ False) → (p2 ∧ p4)) → (p4 → p3))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157176709428118773474775055782 : (((((((p1 ∧ (p2 ∨ (p3 ∨ False))) ∨ p5) → True) ∨ (False ∨ ((p3 ∨ p2) → p4))) → p4) → p1) ∨ (((p5 ∧ (p1 ∨ p2)) ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330871555757469572872796940912 : (True → (p3 → ((p1 → ((p1 ∨ p2) ∧ p2)) → ((p5 → p1) → ((((False → p3) ∨ p4) ∨ (p1 ∨ p5)) ∧ (((p5 → p1) ∧ False) ∨ True)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555491931710645220235289801813 : (((p2 ∨ (p5 → ((((p2 ∧ p4) ∨ (((((p4 → p5) ∨ True) → p5) ∨ p3) → (p5 ∧ (p3 → (p2 ∧ (False ∧ False)))))) ∧ p1) ∨ p5))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342280054673479798214673927560 : (p2 → ((((p1 ∨ (p2 ∨ ((False ∨ (True ∨ (p3 ∧ p3))) ∧ (False ∨ p2)))) → p1) ∧ (p1 ∧ p2)) ∨ ((p1 ∨ p2) ∨ (p2 ∧ (False ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230304029824882392605295950396 : (((p1 ∨ p2) ∧ p2) → (((((((p5 ∨ p4) → p5) → p4) ∨ p2) ∨ (((True → (p4 ∨ True)) ∨ (p3 ∧ p2)) ∨ False)) ∧ p2) ∨ (True → p4))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713457410598382499114186168845 : ((((p3 → (((p5 → p4) → p4) ∨ p4)) ∨ (((p5 → False) ∧ (p3 ∧ (False ∧ ((p5 → (p1 ∨ (p5 → p4))) ∧ (p1 ∧ p3))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_807387168554378401149516044969 : (((p4 → ((p2 ∧ (p4 ∨ (((p3 ∨ p3) ∧ (p5 ∨ True)) ∧ p1))) ∨ ((((False ∧ (p3 → (p1 ∨ False))) ∧ False) ∧ p4) ∧ (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_629864422145908508417632491739 : (((((((p4 ∨ ((p4 ∧ (p5 ∧ p1)) → p1)) ∨ p2) ∧ ((((p2 ∧ True) ∨ (True ∨ p2)) ∧ False) → ((p1 → p5) → p4))) ∨ p3) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115985766838592225108618086588 : ((((p5 ∨ (p2 ∨ p1)) ∨ p2) → (((False ∨ ((((p2 ∧ p4) ∧ (True → p4)) ∧ p1) ∨ True)) ∨ ((p5 → True) ∧ True)) ∨ p3)) ∨ (p3 ∧ p4)) := by
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
    case inr h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
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
      case inr h6 =>
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
  case inr h7 =>
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
theorem thm_5_vars_141736477212434170232083554441 : (((True → False) ∧ ((False ∨ (((False ∨ ((True ∨ p3) ∧ (p1 ∨ (p4 ∨ p4)))) → False) ∨ p1)) → ((p4 → True) → p2))) → (p3 → (p1 ∧ True))) := by
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
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68600369802620267873220282820 : ((p4 → ((((p2 ∨ ((True ∧ p5) ∨ (False ∨ (((((p5 ∧ p5) ∨ p2) ∧ p1) ∨ (p4 → False)) ∨ (False ∧ p3))))) ∧ p2) ∨ p3) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724500377715733299316462952489 : ((((False ∨ (p4 ∧ False)) ∧ ((((p1 ∧ p3) ∨ ((((p5 ∧ p3) → (False ∧ p4)) → (p2 ∧ p2)) ∧ p5)) → (False → (False ∧ p3))) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_717075010629867504207632569677 : ((((True ∨ ((p1 → True) → p2)) ∧ ((((p4 ∨ p2) ∧ (((False ∨ ((p4 ∨ p4) ∧ p4)) → False) → False)) → ((p2 ∨ p2) ∧ p5)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112868026032312548340750287650 : (((((p2 → False) ∧ p1) → ((((p5 ∨ (p4 → p2)) ∨ p3) ∧ ((p4 ∨ (True → p1)) ∧ (True ∧ (p3 ∨ p1)))) ∨ p3)) → p4) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60506371693488778832063455212 : ((True ∧ (((p1 ∧ p1) ∨ (False ∨ (((p5 ∨ (p3 ∨ p4)) ∨ True) ∨ (((p5 → (p1 ∧ p1)) ∧ ((p3 → p4) → p4)) ∧ p5)))) ∧ True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245860019135046655115227026274 : ((p3 ∧ p4) ∨ ((p5 ∧ (p3 → p4)) → (p4 ∨ ((((p5 → ((p3 ∧ True) ∧ (p5 ∨ p4))) ∨ ((True ∨ p3) ∨ p1)) ∨ False) ∧ (p5 ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233480542429202718845504869547 : ((p1 ∨ (False ∧ p1)) → ((True → (p4 ∨ False)) ∨ ((p3 ∧ p4) ∨ ((((p4 ∧ (((p5 ∨ p5) ∧ (False → p3)) ∨ p5)) ∨ True) ∨ p1) ∨ False)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192753222818635843790396661706 : ((((p4 → p3) → (((True ∨ p5) ∧ p3) → p2)) → p2) → ((((p2 ∨ (p2 → p2)) ∧ (((p3 ∨ p4) → p3) ∨ (True ∨ True))) ∨ False) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606626125697671813616793681505 : ((((((False ∨ (p4 → (((((p5 ∨ p4) → True) ∨ ((True ∨ p5) → (p1 ∨ (p3 ∧ (False → p4))))) → p2) ∧ p2))) → p1) ∧ p1) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2871420678866872440821611728 : (((True ∨ False) ∨ p1) ∧ (((True ∧ (p4 ∨ p2)) ∨ ((p5 ∨ p5) ∨ (False ∨ (True ∧ ((p3 → (p2 → (p3 ∨ p2))) ∨ p5))))) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55052641891420877775381012899 : (((False ∨ (False ∨ ((p2 → p4) → p4))) ∧ (p3 ∧ (((((True ∧ p3) → (p3 ∧ (((p1 ∨ False) ∧ p4) ∨ True))) ∧ p5) → p5) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261257185815263409859387321469 : ((p5 → True) → ((p5 ∨ (((p4 ∨ (p2 → True)) ∨ ((((((False ∨ p3) → p5) ∨ p5) ∧ (False ∧ (False ∨ p1))) → p4) ∨ p2)) → p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



