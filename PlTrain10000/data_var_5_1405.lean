variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620790437822162850794559675661 : (((((p5 ∧ p3) → (((p4 ∧ p1) ∨ True) ∧ ((((p5 ∨ p5) ∨ (False → p3)) ∨ p1) → ((p3 ∨ ((p1 ∨ p3) ∧ False)) ∧ p4)))) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_172363812417536584858549426518 : ((((p4 ∧ p5) ∧ (p4 ∨ (False ∧ p3))) ∨ (((False ∧ (True ∧ p2)) → p2) → True)) ∨ (((True → ((p2 → p1) → (p5 ∧ False))) ∨ p1) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217636443918250733081809908830 : ((((p3 ∧ p3) → p1) → p4) → ((((p2 ∧ False) ∨ (False → p1)) → p2) → (p4 → (((p1 ∨ (p4 ∨ p5)) ∧ (p5 → (p3 → True))) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118742209937717901817659726160 : ((p5 ∨ ((((p1 ∨ p1) ∨ p3) → (p4 → p3)) ∧ (((p2 ∨ (False → (p3 ∨ ((p3 → p1) → (p5 ∧ p1))))) → p3) ∧ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737559184690742274469995208053 : ((((p5 → p1) ∧ ((((False → (p5 ∨ p5)) ∧ (((p4 → p1) ∧ ((True ∨ p2) ∨ ((p1 ∨ p4) → True))) ∨ p1)) → (p5 → p2)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322415032102807439985761414059 : (p5 ∨ (((((p1 ∧ ((p1 ∧ False) → False)) ∨ (p2 ∧ p1)) ∧ p3) → ((((False ∨ p1) ∧ (p5 ∧ (p2 → (p2 ∨ True)))) ∨ p4) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185262010689245295107496475540 : ((p1 ∧ ((p2 → (p1 → False)) ∨ ((p2 → (True ∨ p3)) → p3))) ∨ (((((p2 → p1) → p5) → ((p3 ∨ p5) ∨ False)) ∧ (False → p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185342436461293132008059815173 : ((p4 ∧ ((((p1 ∨ (p3 ∨ p3)) ∨ (p4 ∨ p1)) ∨ p3) → p3)) ∨ ((((p2 ∧ p3) ∨ ((p2 ∧ p4) → (p2 ∨ (p3 ∧ p3)))) ∨ p1) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651363905401854477255597121633 : (((((p4 ∧ (p2 ∧ p4)) ∨ (((((((p3 → p2) → p3) → p1) → (p1 → p4)) → (p1 → p3)) ∨ (p1 → p3)) ∧ False)) ∧ (False ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777441641464581557522953922475 : (((p1 ∨ ((((((p5 ∧ p1) → p4) ∨ (p2 → p3)) ∨ ((True → (p2 ∨ p4)) ∨ False)) ∨ False) → (p1 ∧ (((p3 ∧ p5) ∧ p2) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337539341959939043065845850671 : (p1 → ((((p2 ∧ (p3 ∨ True)) ∨ (True ∨ p2)) ∧ (p3 ∧ (((p3 ∧ p4) → (True ∨ (False ∧ p2))) → p2))) ∨ (True ∧ (p3 ∨ (p2 → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336081818751327611937071707792 : (p1 → ((((p2 → (p4 ∨ ((((p5 ∧ p2) ∨ p1) ∨ ((p2 ∨ True) ∨ p1)) ∧ (p2 → p3)))) ∧ (p4 ∧ ((p5 ∧ p5) ∧ p5))) ∧ p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318557172840845014786704054151 : (p4 ∨ (((((((p4 ∨ (p2 ∨ p1)) ∧ ((p3 → (False ∧ p1)) ∨ p2)) ∨ p5) → False) ∧ ((p2 ∧ p1) → (p1 ∨ True))) ∨ p3) ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204429253840594046208508808887 : (((((False ∧ p5) ∧ True) ∧ p4) ∨ p2) ∨ (p5 → ((p5 → ((p4 ∧ p3) ∨ ((p5 ∧ False) ∨ (True ∨ False)))) ∧ (p1 → (p4 → (False → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161432441825163647090286843784 : ((p2 ∧ (((p2 ∧ False) → ((p2 ∧ p2) ∨ p1)) ∨ (((p2 ∨ p4) ∧ (p4 ∨ p5)) ∧ (False → p3)))) → (True ∧ ((p4 ∧ (p2 → p1)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h5
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h9 := h4 h8
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h18 := h4 h17
        -- One of the premise coincides with the conclusion.
        exact h18
      case inr h19 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h20 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h21 := h4 h20
        -- One of the premise coincides with the conclusion.
        exact h21
    case inr h22 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h23 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h24 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h25 := h4 h24
        -- One of the premise coincides with the conclusion.
        exact h25
      case inr h26 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h27 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h28 := h4 h27
        -- One of the premise coincides with the conclusion.
        exact h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804955905621490129727892342580 : (((p3 → ((p5 → False) ∨ (((((p1 → p2) → ((p3 ∨ p5) → True)) ∨ ((p5 → ((p5 ∧ p2) → (p1 → p5))) ∧ p1)) → False) ∨ p3))) ∨ p3) ∧ True) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174581213185929590025645953645 : (((((p2 ∧ p4) → p5) ∧ False) ∨ (True → (False ∧ (False ∧ (p3 ∧ (p5 → p4)))))) → ((p4 ∧ (p2 → ((p5 ∧ (p3 ∨ True)) ∧ p2))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- We need to get the left conjuct of h7 based on <expert-advice>.
    let h8 := h7.left
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152299773474885726859106567560 : (((p3 → ((True ∨ False) ∨ (p5 → p4))) → (((False ∧ (((p2 ∨ p2) ∧ (p4 → p1)) ∧ False)) → p3) ∧ p4)) → (False ∨ (p3 ∨ (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138280610589486502565626302277 : ((p3 → (((((p4 ∨ (p2 ∧ p2)) ∧ p2) ∧ p1) ∧ (((((p5 ∨ p1) ∧ p5) → p2) ∨ True) ∨ (p5 → p5))) ∨ p3)) ∨ (p5 → (False ∧ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159478741240671695208475744541 : ((((((p1 ∨ p4) ∨ p4) ∧ p3) ∧ (p5 → ((((p5 ∧ p1) ∨ p2) ∨ True) → (p4 → p5)))) ∧ p1) → ((p5 ∨ p3) → ((p2 ∨ p4) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h1.left
    let h16 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h17 := h15.left
    let h18 := h15.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h20
    case inr h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_705586189273654446058508084906 : (((((p1 ∧ (p3 → ((True ∨ p4) ∧ True))) → False) ∧ (False → (True → (((((p1 ∧ (p3 ∧ True)) ∧ p1) → True) ∨ False) → (p5 ∧ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124305313729614583584915296537 : ((((True ∨ ((p2 → False) → p2)) → (True ∧ p3)) ∧ (((((p1 → ((p3 → p4) ∧ p3)) ∨ p1) → p1) ∧ p2) ∧ (p3 ∧ p3))) → (p4 ∨ p3)) := by
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
  let h8 := h5.left
  let h9 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173289204859488275050930986435 : ((p1 → ((((p1 ∧ p5) ∨ False) ∨ ((p4 → (p1 ∧ (True ∨ False))) → p4)) ∨ p1)) ∨ (False ∨ ((p4 ∧ p3) → (((p3 ∨ p3) ∧ p2) → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642736149496936546541629215636 : ((((p1 ∧ ((p4 ∨ p3) → (((p2 ∨ p5) ∨ ((True ∨ p5) ∧ p4)) ∧ (p2 ∧ ((p5 ∨ True) ∨ (p1 ∨ ((p1 ∧ p3) → p4))))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51587424905607119589795442813 : (((False → ((p2 ∧ (False ∧ (p4 ∧ ((False ∧ ((p1 ∧ True) ∧ p2)) → p5)))) → (p1 ∨ p1))) → ((True → (p3 ∧ p2)) ∨ (False → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112345419015137920400690086619 : (((p5 → ((p4 ∧ p5) ∨ ((((p4 ∧ (p1 ∨ (p1 ∧ p3))) → ((p5 ∨ (p2 ∧ p4)) ∨ False)) → p1) ∧ (False ∧ p4)))) ∨ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161551777458733351226819290429 : ((p5 ∧ (True ∧ ((True ∧ (p4 ∧ (((p4 ∨ (p2 ∨ ((p4 ∧ p2) → False))) ∨ p4) ∧ p3))) ∧ p5))) → ((True → (False ∧ (p1 ∧ p2))) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
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
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h18 := h2 h17
      -- We need to get the left conjuct of h18 based on <expert-advice>.
      let h19 := h18.left
      -- False on the left can always be used.
      apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h22 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h23 := h2 h22
        -- We need to get the left conjuct of h23 based on <expert-advice>.
        let h24 := h23.left
        -- False on the left can always be used.
        apply False.elim h24
      case inr h25 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h26 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h27 := h2 h26
        -- We need to get the left conjuct of h27 based on <expert-advice>.
        let h28 := h27.left
        -- False on the left can always be used.
        apply False.elim h28
  case inr h29 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h30 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h31 := h2 h30
    -- We need to get the left conjuct of h31 based on <expert-advice>.
    let h32 := h31.left
    -- False on the left can always be used.
    apply False.elim h32



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41655700764354852504063628199 : ((((True ∧ (((False → p1) → True) ∨ p1)) ∧ (((p3 ∧ p1) ∧ (p5 ∨ p5)) ∧ (((p1 ∨ True) ∧ ((p4 → p1) ∨ True)) → p1))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190992167982307690362728938430 : ((((p3 ∨ False) ∧ (p3 → p2)) ∨ (p4 ∨ (p4 ∨ p4))) ∨ ((((False ∧ p5) ∧ p5) ∧ (((p4 ∨ False) ∧ (p2 ∨ (p3 ∨ True))) ∨ p4)) → p2)) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_224185477919765899292378010997 : ((True → (True ∨ p1)) ∧ ((p3 → (p5 → ((False → False) → False))) → ((((p3 ∨ p4) ∧ (p2 → ((p5 → p4) ∧ p2))) → (p2 → False)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32725345162069189794434840199 : ((p2 ∨ (False ∨ ((p5 → (p1 ∧ False)) → (((((p4 ∧ False) → p3) → False) ∨ True) ∨ (((p5 ∧ False) → p1) → (p5 → (p2 ∨ False))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708571224220213598008678422754 : ((((((p1 → False) ∨ ((True → p3) ∨ p4)) ∨ p4) → ((p3 → (p1 ∨ (p3 ∨ p3))) → (p2 ∨ ((p5 ∧ (p5 ∨ (p3 ∨ p4))) ∨ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302853238002146347027711296545 : (False ∨ (p5 ∨ (p5 → (((p3 ∨ ((((True → ((p3 → ((p5 → p1) ∨ p5)) → False)) ∧ (p5 ∨ p1)) → p3) → (p3 ∨ p5))) → p4) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207319209600341482028055768937 : ((((p4 ∨ True) ∧ (p5 → p2)) ∨ p3) → (((False → p5) → ((p2 → p2) ∧ True)) ∧ (((((p3 ∨ p2) → p4) ∨ False) → (p1 → p1)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h9 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h10
  -- Implications on the right can always be decomposed.
  intro h11
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h18 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h19 =>
    -- False on the left can always be used.
    apply False.elim h19
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232788500650217466963843878425 : ((p2 ∧ (p3 ∧ p1)) → ((((p2 → (p3 → (p4 ∧ ((p3 ∧ (False ∧ p4)) ∨ p1)))) ∨ ((False ∧ p4) ∧ False)) ∧ (False ∨ (p5 ∧ p1))) ∨ p3)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180253166561291020281512836056 : (((p1 ∨ (p1 ∨ (False → (False ∧ (True → (p1 ∨ (p5 → p2))))))) → p4) → ((p3 ∧ ((p3 ∧ True) → p5)) ∨ ((True ∧ (p4 ∨ p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p1 ∨ (p1 ∨ (False → (False ∧ (True → (p1 ∨ (p5 → p2))))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66370396364113443123758280912 : ((p5 ∨ (p2 ∨ (((((p2 → (((p1 → p3) ∧ p1) ∨ (p3 → (p5 ∨ p1)))) ∨ False) ∨ p2) → (((p5 ∧ p5) ∨ p4) → p1)) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113480512937561477709252400908 : (((((p3 → (p5 ∧ (((True ∧ ((p3 → (False ∨ p4)) → False)) → p5) → (p1 → p4)))) → p5) ∨ (p3 ∨ p4)) ∨ (p5 ∨ False)) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116026455695747506401496167492 : (((p3 ∧ ((p5 ∨ p4) ∧ p4)) → (p3 ∧ ((p4 ∨ (True ∨ (p2 → p1))) → (((False ∨ (p5 ∧ (p5 ∨ p3))) → p4) ∧ False)))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55832689799267626154819281442 : (((True ∧ (p5 → (False ∧ p1))) ∧ (p4 ∨ (p4 ∧ (((False ∧ False) ∨ (p1 ∨ (p4 ∨ p5))) → (((p1 ∧ p2) ∨ p3) → (p2 ∧ p3)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646777187614427364225515567832 : ((((p2 → ((((False ∨ ((((False ∧ True) ∨ p1) → (p1 ∧ True)) ∧ (False ∧ (p4 ∨ p3)))) ∧ True) ∨ p3) ∨ (p2 → (p4 ∨ p2)))) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85403770665392082538398376598 : ((((p3 ∧ True) ∧ (((True ∧ False) → p4) → ((False → p1) ∧ False))) ∧ ((p5 ∨ ((p3 → ((p3 → True) ∧ True)) ∨ p1)) ∨ (True → p4))) → p5) := by
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
  cases h3
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h12 : ((True ∧ False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h16 := h5 h12
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h19 : ((True ∧ False) → p4) := by
          -- Implications on the right can always be decomposed.
          intro h20
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- False on the left can always be used.
          apply False.elim h22
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h23 := h5 h19
        -- We need to get the right conjuct of h23 based on <expert-advice>.
        let h24 := h23.right
        -- False on the left can always be used.
        apply False.elim h24
  case inr h25 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h26 : ((True ∧ False) → p4) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- Conjunctions on the left can always be decomposed.
      let h28 := h27.left
      let h29 := h27.right
      -- False on the left can always be used.
      apply False.elim h29
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h30 := h5 h26
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- False on the left can always be used.
    apply False.elim h31



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193700516994582822709476631078 : ((p1 ∧ (p2 ∨ (((p2 → p3) → p1) → (False ∧ p3)))) → (((p3 ∨ (((p4 ∨ False) → p4) ∧ True)) → ((p3 → p2) ∧ True)) ∨ (False ∧ p4))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h6
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h4
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h11 =>
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : ((p2 → p3) → p1) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h12
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4411997359268303030282943355 : (p1 → (((p5 → True) ∧ ((((p4 ∧ p3) ∨ p1) → p5) ∨ p5)) ∨ (((((True ∨ p2) ∧ False) ∧ ((p3 ∨ False) → p5)) ∧ True) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233170318950301979768163493068 : ((p5 ∧ (p1 ∨ False)) → (((((p5 ∧ True) ∧ False) ∨ (True → (False ∧ ((p2 ∨ p4) → False)))) ∨ p1) ∧ (True → ((p4 ∨ (False ∨ True)) ∧ True)))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223553610542830674015823818380 : ((False ∨ (p5 → p5)) ∧ (p4 → ((True → (((p5 ∧ ((p3 ∨ (p5 → p5)) ∨ (True ∧ (p4 ∧ p4)))) → False) ∧ (False → (p4 ∨ p3)))) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722119252771113564498458100704 : ((((p3 → ((p2 → p2) ∧ True)) → ((((p5 → p1) → (p1 ∨ (p4 ∨ p1))) → ((True → False) ∨ (False → (p5 ∨ (False ∨ p4))))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625925022081307135871688690007 : ((((p2 → ((((True → False) ∨ p3) → ((p3 ∨ p1) ∨ (p3 ∧ (p4 ∧ ((p2 ∨ p5) ∧ (p5 ∧ (p5 → False))))))) ∧ (True ∨ p5))) ∨ p5) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153264371787645481164317825199 : ((False ∨ (((False → p2) ∨ p2) ∧ (p5 ∨ (((p1 ∨ ((p3 ∨ p2) → p1)) ∧ (p5 → True)) → (p3 ∧ p2))))) → (p2 ∨ (p2 ∨ (False → p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h7 =>
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h12 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357033609991831631619027559395 : (p5 → ((p3 ∧ (p5 ∧ False)) ∨ ((((p1 ∨ ((p3 ∨ (p4 ∨ p1)) → True)) → False) ∧ ((p1 → (False ∨ p3)) → ((False ∨ p1) ∨ p1))) → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p1 ∨ ((p3 ∨ (p4 ∨ p1)) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114628780452290215600718839372 : (((((p3 ∧ (((p2 → (p4 ∨ (p4 ∨ p3))) → p2) ∧ p1)) → (p5 ∧ True)) ∨ p5) ∨ (p5 ∧ ((p2 ∨ (False ∨ p5)) → p3))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_442243420901921870806960023905 : (((((((p3 → p4) ∨ (((((True ∧ p3) → p4) → True) ∧ ((p2 ∧ p2) ∧ p2)) ∨ p4)) ∧ (p2 ∨ p3)) ∨ True) ∨ (p3 ∨ (p3 ∨ p4))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797884199902667626003011102458 : (((p1 → ((((p4 → (p4 ∧ False)) → False) → (p1 → ((((p1 ∧ p2) → (p5 → (p5 ∧ p3))) → (p5 ∧ False)) ∨ p5))) ∨ (p2 → p2))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738848767428204088174905532342 : ((((p2 ∧ p5) ∨ (p4 ∨ ((p3 → (p2 → p5)) → (((p3 → p2) ∨ (p1 ∨ (True → ((p4 → False) → (p5 ∧ p4))))) ∨ (p1 → True))))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47278136750203927034722822859 : (((((True → p2) ∧ (p2 ∧ p5)) ∨ (p3 → ((True → ((p5 ∧ (p4 → True)) → ((p1 → (p2 → p4)) ∨ p5))) ∨ True))) ∨ (p1 → False)) ∨ p4) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737586895281488436478314315337 : ((((p5 → p1) ∧ (False ∨ ((True ∨ (p5 ∨ ((((p2 → ((p5 → (((p5 → p5) ∨ True) ∨ p3)) ∧ p2)) ∧ p4) ∨ True) → p1))) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348807879306555276470767072706 : (p3 → (p1 ∨ ((False ∨ ((((((p2 ∨ True) ∨ True) ∨ False) → p1) → p1) → (p5 ∧ (p5 ∧ p3)))) ∨ ((((p3 ∨ p5) → p3) ∨ False) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117261181120175229821321984549 : ((True ∧ (p5 → (p2 ∨ ((False → p1) ∧ (((p1 → ((p5 ∨ (p2 ∨ ((p5 ∧ p5) ∧ (p5 → True)))) ∧ p4)) → False) ∨ p3))))) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304787844402716336147735272849 : (p1 ∨ ((p4 → (((((((p3 ∨ (p2 ∧ (True ∧ p2))) → p3) ∧ p1) ∧ (p3 → (p3 ∧ False))) ∧ p2) ∧ p3) ∧ (True ∧ False))) ∨ (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148593430268337529984240864119 : ((((p4 ∨ p1) ∧ ((False ∧ (p1 ∨ False)) ∨ (p4 → False))) ∨ (((p3 → (p2 ∧ p5)) ∧ True) ∨ (False → p1))) ∨ (p5 ∨ (p5 ∨ (p4 → False)))) := by
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
theorem thm_5_vars_876316287673205413745240990229 : ((((((((p5 ∨ False) ∨ False) → p4) ∨ ((False → p5) → (((False ∧ p3) → False) ∨ (p4 ∧ (p5 ∨ p4))))) → (p2 ∧ p1)) ∧ (p4 → p4)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((((p5 ∨ False) ∨ False) → p4) ∨ ((False → p5) → (((False ∧ p3) → False) ∨ (p4 ∧ (p5 ∨ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h4
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- One of the premise coincides with the conclusion.
  exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317618460436941701583377692809 : (p4 ∨ (((((p1 → (True ∧ (p1 → p5))) ∨ (((False → (p4 ∧ p3)) → p3) ∨ (p5 ∧ ((p2 → p1) → (p1 ∨ p5))))) ∨ True) ∨ False) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244589601682615167171955190653 : ((False ∧ p4) ∨ ((p4 → p2) → (((((p1 ∨ p4) ∨ (p3 ∧ p5)) ∨ (p1 → p5)) ∧ ((p2 ∨ ((True ∨ p3) → (p3 → p4))) → False)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157168975245420543100909787448 : ((((((p5 ∧ ((p2 → True) ∧ p2)) ∧ (False ∨ (((p5 ∨ p4) → True) ∧ p3))) ∨ p2) → True) → p5) ∨ ((p1 ∨ ((p4 ∨ p5) ∧ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223877615982970071307519744022 : ((p3 ∨ (False → p3)) ∧ (((((p2 ∧ ((p3 ∧ (False ∧ p1)) → (p2 ∨ True))) ∨ p4) ∧ True) ∧ (((p2 ∨ p2) ∨ p1) ∨ p1)) ∨ (p3 → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158797690194112507112224598732 : ((p5 ∧ ((((False → p2) ∧ (p3 ∨ True)) → p4) → (((p3 ∧ True) ∧ p3) ∨ (p3 ∨ (p1 → p3))))) ∨ (p2 → ((p5 ∨ (p3 ∧ True)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778112206216052150197353610046 : (((p1 ∨ ((p2 ∧ p1) ∨ (((True ∧ p3) ∨ (p4 → (p4 → (((p5 → p3) ∧ (((p3 ∨ p2) → (p4 ∨ p5)) ∨ p5)) ∨ p4)))) ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330980446134507480011615781984 : (True → (p5 → (((p2 ∨ (((False ∨ p2) ∧ p1) ∨ p3)) ∧ (p3 → ((((False ∧ p2) → p4) → (p5 ∨ p2)) → p4))) → (p4 ∨ (False → p4))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356434479804002047590493821455 : (p5 → ((((p5 ∨ p4) → (((False ∨ p1) ∨ p2) ∧ (False ∧ p3))) ∨ p3) ∨ (((True ∨ (False ∨ ((p4 ∧ (False ∧ False)) ∧ p5))) → p4) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185967197299937162398823183229 : (((p1 ∧ ((p1 ∧ p1) → ((p4 ∨ (p5 → p5)) ∨ False))) ∧ p3) → (((p5 → p3) → (p4 ∨ ((False → True) ∧ False))) → (p4 ∨ (p4 ∧ p5)))) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h7 : (p5 → p3) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h9 := h2 h7
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157925188262145537005484762784 : (((((p2 ∨ (p3 ∨ p5)) ∨ (p3 ∧ p5)) ∧ False) ∧ (((p3 → ((False → p1) ∧ p2)) → p1) ∨ False)) ∨ (p5 → (p4 → (p4 ∧ (p5 ∧ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682667778188524769599506921891 : ((((((p4 → (True → (True ∧ p4))) → p4) ∨ ((((p1 ∨ (p1 ∧ p1)) ∧ p3) ∨ p3) ∨ p2)) ∧ ((p4 ∧ (p3 ∧ p1)) ∨ (p3 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60989095231107196069921761225 : ((False ∧ (((((((p2 ∧ (False ∧ p1)) ∨ p4) ∧ (p3 → ((p4 → p3) ∨ p1))) → p5) → (False ∨ ((True ∧ True) → p4))) ∨ p1) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_73672609565152847729120031430 : (((((p2 → ((p4 ∨ (p5 ∧ (p3 → ((p1 ∧ p3) → False)))) ∨ (True ∨ True))) → p3) ∧ ((p4 ∧ ((p3 → p5) ∨ p4)) ∨ p1)) ∨ False) → p3) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h9 : (p2 → ((p4 ∨ (p5 ∧ (p3 → ((p1 ∧ p3) → False)))) ∨ (True ∨ True))) := by
          -- Implications on the right can always be decomposed.
          intro h10
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h9
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p2 → ((p4 ∨ (p5 ∧ (p3 → ((p1 ∧ p3) → False)))) ∨ (True ∨ True))) := by
          -- Implications on the right can always be decomposed.
          intro h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h15 := h3 h13
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : (p2 → ((p4 ∨ (p5 ∧ (p3 → ((p1 ∧ p3) → False)))) ∨ (True ∨ True))) := by
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h19 := h3 h17
      -- One of the premise coincides with the conclusion.
      exact h19
  case inr h20 =>
    -- False on the left can always be used.
    apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_687219749567433611596589321786 : (((((((((p4 → (p5 → p1)) ∧ p4) ∧ ((False ∧ p4) ∨ p3)) ∨ p2) ∧ p5) ∧ p4) ∧ (p2 ∧ ((p3 → p5) → ((False → p4) ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318863980905346789191112216313 : (p4 ∨ (((p4 ∧ ((False ∨ ((((False → p2) ∨ True) ∨ p4) → (p5 ∧ ((p5 ∨ p5) ∧ True)))) ∧ False)) ∧ (p1 ∨ p3)) ∨ ((p4 → p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136541186835696892166409509426 : ((((p2 ∧ p4) ∧ p5) ∨ ((((((False ∨ (p1 → False)) ∧ p3) → p1) → ((p4 → (p3 ∧ p3)) ∧ False)) ∨ p1) ∨ True)) ∨ ((p1 → p2) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257881872533156203854207782132 : ((p4 ∨ True) → ((True ∧ ((p2 ∨ p5) ∧ p5)) → (((p4 ∨ ((p3 ∨ p3) → p5)) → (p3 ∧ (False ∨ p1))) → ((p5 → (p4 → p1)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p4 ∨ ((p3 ∨ p3) → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the right conjuct of h13 based on <expert-advice>.
      let h14 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- False on the left can always be used.
        apply False.elim h15
      case inr h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Implications on the right can always be decomposed.
      intro h19
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h20 : (p4 ∨ ((p3 ∨ p3) → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h21 := h3 h20
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- False on the left can always be used.
        apply False.elim h23
      case inr h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h27
      -- Implications on the right can always be decomposed.
      intro h28
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h29 : (p4 ∨ ((p3 ∨ p3) → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h28
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h30 := h3 h29
      -- We need to get the right conjuct of h30 based on <expert-advice>.
      let h31 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h31
      case inl h32 =>
        -- False on the left can always be used.
        apply False.elim h32
      case inr h33 =>
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h35
      -- Implications on the right can always be decomposed.
      intro h36
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h37 : (p4 ∨ ((p3 ∨ p3) → p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h38 := h3 h37
      -- We need to get the right conjuct of h38 based on <expert-advice>.
      let h39 := h38.right
      -- Disjunctions on the left can always be decomposed.
      cases h39
      case inl h40 =>
        -- False on the left can always be used.
        apply False.elim h40
      case inr h41 =>
        -- One of the premise coincides with the conclusion.
        exact h41



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774192419994061134191955637129 : (((False ∨ ((((p2 → ((False ∨ (((p1 → (p3 ∧ p3)) → (p5 ∧ (p1 ∧ p1))) ∨ True)) ∨ True)) ∨ p2) ∨ p2) ∧ (p5 ∨ (False ∨ True)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214797171680945303077905542980 : (((p1 ∨ p5) ∨ (p2 ∨ False)) ∨ (((p3 → p4) ∨ ((p5 ∨ (((True → p4) → p1) → p5)) ∨ (True ∨ ((p1 ∧ p4) → (False → p1))))) ∨ False)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_641426878879287528677972515522 : (((((p5 → True) ∨ (False ∨ (((((((p5 ∨ (False → p5)) → p1) ∧ (True ∧ p4)) ∧ p3) ∨ (p4 ∧ p1)) → False) → (False → p3)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190644899225778018391278683227 : (((p1 ∨ (((p2 ∧ (p3 ∨ p4)) ∧ True) → p1)) → p4) ∨ (p4 → ((((False → (p5 ∧ (((p5 → p5) ∧ p3) ∨ p3))) ∨ p5) ∨ p5) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57650190782295065004896693274 : ((((p1 ∨ p4) ∨ True) → (False ∧ (((True ∧ p1) ∨ (p3 ∧ False)) ∧ ((((((True ∧ p4) ∧ False) ∨ p3) ∧ p5) → (p5 → p3)) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54563561561298606487880713574 : (((p4 ∧ (p3 ∨ ((p1 ∧ (True → p3)) → p5))) ∨ (p5 → ((p1 → ((p5 → (p5 ∨ p1)) ∧ p1)) → (p3 ∧ ((p3 ∧ p3) → p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729911649091602691637936849767 : (((((p3 ∧ False) → True) → (p2 ∨ (((p5 ∧ p4) ∧ (p3 ∧ ((p1 ∨ p3) → p5))) ∨ ((False → p5) ∨ ((p4 ∧ p1) ∧ (True ∧ p2)))))) ∨ p5) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226356775495979400059654874314 : (((True → False) ∨ p2) ∨ ((p3 ∧ ((p2 ∨ (True ∧ (p2 ∨ p2))) ∧ False)) ∨ (((True ∨ (((True ∧ False) → p1) ∨ p3)) ∨ (False ∧ p5)) ∨ p5))) := by
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
theorem thm_5_vars_336380399690591836186249682804 : (p1 → ((False ∧ ((p2 ∨ (p2 → (p1 ∧ (False ∧ (True ∧ ((p4 ∨ p2) → (p5 ∨ (p2 ∧ (p3 → p3))))))))) → (p4 → (p3 ∧ p3)))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601574626261845661564582899918 : ((((p3 ∧ (((p4 → (p3 ∧ (p5 → (p3 ∨ p3)))) ∧ p5) ∨ (False ∧ (((p3 → (((p3 ∨ p5) ∨ True) ∧ True)) → p5) ∧ p5)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344306108005755738771483684689 : (p2 → (p3 ∨ (((((p2 ∧ False) → (p4 ∨ (p4 ∧ True))) ∨ p3) → ((p2 ∧ (True → False)) → p3)) ∨ (p5 ∨ ((p3 ∨ p4) → (p5 ∨ True)))))) := by
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
theorem thm_5_vars_231710338194304276401576131798 : (((p2 ∧ False) → p2) → (p3 → ((p5 ∧ (p4 ∧ ((False → (p1 ∨ (p4 ∧ (p5 → (p2 ∧ False))))) → False))) ∨ (True ∨ ((p4 ∨ p2) ∧ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_848116905588834275681682506 : ((p1 ∨ ((p3 ∨ p4) ∨ (((False ∨ p3) → ((((p4 ∧ p3) → p1) ∧ ((True → ((p5 ∨ p3) ∧ False)) → p1)) ∨ True)) ∨ p4))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_573861833188244473917276295798 : (((p2 → ((False ∧ ((p3 ∨ (True ∨ p3)) → (((p3 ∨ p3) → ((((False ∨ p4) → (p4 ∧ p2)) ∧ (p1 ∨ p4)) ∧ p4)) → p4))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_214529192028222890401763296935 : (((p5 ∧ p3) ∧ (p4 ∧ p5)) ∨ ((p4 ∧ ((p2 ∨ (((p4 → p5) ∨ ((((p5 ∨ p2) ∧ p2) ∧ p1) → False)) ∧ p1)) ∨ p3)) → (False ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776305777922010023231261273129 : (((p1 ∨ ((True ∧ ((p1 ∧ (p3 ∧ p1)) ∧ (((p1 ∧ (p4 ∧ (p5 ∧ (p3 ∨ ((p3 ∨ (p1 ∧ p1)) ∧ False))))) ∨ p5) → p2))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657742624821401572182793227822 : ((((True ∧ ((((p1 → (p3 ∨ (((p4 ∧ p2) → ((p5 ∨ p2) → p5)) ∧ ((p4 ∨ p2) ∧ p4)))) ∧ p5) ∧ p3) → p2)) ∨ (p4 → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321319769851773507314573198060 : (p4 ∨ (p5 ∨ (((p3 ∨ True) → ((p5 → p2) ∧ p3)) → ((((((p5 ∧ p4) ∨ p1) ∨ (p3 ∨ p3)) → False) → (False ∧ (p1 ∨ p1))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p5 ∧ p4) ∨ p1) ∨ (p3 ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h8 : (((p5 ∧ p4) ∨ p1) ∨ (p3 ∨ p3)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h9 := h5 h8
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51442254302462002153318046133 : ((((p2 ∧ (False ∧ ((False ∧ ((p1 ∨ p5) ∧ False)) ∨ ((p3 ∨ p5) ∨ False)))) → (p1 ∧ p1)) → ((((p2 ∨ True) → True) → p4) ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135296350943098316848041622656 : ((((False ∧ ((p1 ∨ (False ∧ (p3 ∨ p5))) ∨ (p4 → (False → ((p3 → p3) → p2))))) ∧ p5) ∧ (p1 ∨ (p1 → p1))) ∨ ((p5 → p5) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204364810541573557838766162616 : (((p2 ∨ (p2 ∨ (p3 → p2))) ∧ p4) ∨ ((p4 → (((p3 → (p2 → p1)) ∧ False) ∧ ((p3 → (False ∨ p5)) → True))) → ((p2 ∨ True) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305060099018304116584180268231 : (p1 ∨ ((((((p1 ∨ (p5 → ((p2 → p1) ∨ (p1 → (p5 ∨ p5))))) ∨ p2) ∨ True) ∧ (True → False)) ∧ (p2 ∨ True)) → (p2 → (p4 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h10 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h11 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h12 := h6 h11
          -- False on the left can always be used.
          apply False.elim h12
        case inr h13 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h14 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h15 := h6 h14
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Disjunctions on the left can always be decomposed.
        cases h4
        case inl h17 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h19 := h6 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
          have h21 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h6, we can now drive its conclusion.
          let h22 := h6 h21
          -- False on the left can always be used.
          apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h24 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h26 := h6 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h29 := h6 h28
        -- False on the left can always be used.
        apply False.elim h29
  case inr h30 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h31 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h33 := h6 h32
      -- False on the left can always be used.
      apply False.elim h33
    case inr h34 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h35 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h36 := h6 h35
      -- False on the left can always be used.
      apply False.elim h36



