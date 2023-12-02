variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67759073256739292393297722517 : ((p2 → (((p5 ∧ (((((p2 ∧ True) ∧ p3) ∨ (False ∧ p4)) ∧ (((p5 ∨ p1) ∨ True) ∧ False)) ∧ (True ∨ p3))) ∨ (True → False)) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1499822397618648969653235115 : ((((((False ∨ (p1 → p2)) ∨ p1) ∨ (p3 ∨ (p2 ∧ (p5 ∧ p2)))) ∧ ((p5 ∧ False) ∨ p3)) ∨ (p5 → (p5 ∨ p4))) ∨ (p2 ∧ p2)) := by
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
theorem thm_5_vars_172475238639391939728986032183 : ((((True ∨ (p5 → p2)) ∨ p1) → (((p1 ∧ p2) ∨ (p4 ∧ False)) ∨ (True ∨ p3))) ∨ (p4 ∧ ((True ∨ (p2 → ((p2 ∧ True) ∧ False))) ∨ p1))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45151791231211411950283730454 : (((True ∧ (((((p1 ∧ p1) ∧ p5) ∨ (((p5 ∨ p2) ∨ (p2 ∧ (p1 ∧ p3))) ∨ True)) ∧ (p5 ∧ ((p2 ∧ p2) ∨ p2))) ∨ False)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357425361621057178977092110525 : (p5 → ((p3 ∨ False) → (((p1 → p1) ∧ p2) ∨ (((p5 → ((((p3 → p4) ∨ (p4 → p5)) → p2) ∨ p3)) → False) ∨ (p3 ∨ (p5 ∧ True)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199187554903345754241306198103 : (((p3 ∧ ((p1 ∨ p1) ∧ (p1 ∧ p4))) ∧ p3) → (((False ∨ p2) ∧ (p4 ∨ p2)) ∨ (p1 → (p5 ∨ (((p4 → (p4 ∧ p1)) ∨ True) → p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h7.left
    let h17 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h19
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135397717195756092189980867793 : (((((((True ∧ False) → (p1 ∨ False)) ∧ (p3 ∨ p3)) ∧ p3) ∧ ((p1 → p5) ∧ (True ∧ p1))) ∨ ((p2 ∨ p2) ∧ False)) ∨ ((True ∨ p3) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340732191665365063886952737453 : (p2 → (((((p3 ∧ (p1 → ((((True ∧ (p3 → ((p3 ∨ True) ∧ p5))) ∧ (True → (p4 → p5))) → p4) ∨ p5))) ∨ p5) ∨ p4) ∨ p4) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245205988869228622044666760414 : ((p2 ∧ False) ∨ (p3 ∨ ((False ∨ (p2 ∨ (((False ∧ p3) → ((True ∧ ((p5 → (p2 → p2)) ∧ p2)) ∧ (p1 ∨ p5))) ∨ (p3 ∨ p3)))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782699791461815911123439840610 : (((p3 ∨ (((((p2 ∨ ((True → p3) ∨ ((p1 → p3) → p2))) ∨ ((p5 → ((p4 → p4) → p5)) ∧ p1)) ∧ p1) → (p1 → p3)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199316464045652070138993374155 : ((((p1 ∨ ((True ∧ p2) ∧ p1)) ∨ True) ∨ p5) → (p4 → ((((False → ((p4 ∧ False) ∧ p1)) ∧ p5) → (((p2 ∨ p3) ∨ p5) ∨ p5)) ∨ p3))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h6
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Conjunctions on the left can always be decomposed.
        let h12 := h10.left
        let h13 := h10.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h20
  case inr h21 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h22
    -- Conjunctions on the left can always be decomposed.
    let h23 := h22.left
    let h24 := h22.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165751292673835145092723023843 : (((p1 ∧ (False ∨ (p3 ∧ p1))) ∨ (p3 ∧ ((True ∨ (p2 ∧ (p4 ∧ p5))) ∨ (p3 ∨ True)))) ∨ (True ∨ ((False → p3) ∧ (p2 → (False ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259920937716548986341160136685 : ((p1 → p5) → ((p2 ∨ ((p5 ∧ False) ∧ (p4 → ((((((p5 ∨ p3) ∧ ((p1 ∨ p3) → p3)) ∨ p3) → p1) ∨ p2) ∨ (p1 ∧ p2))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307511181730257964780338175652 : (p1 ∨ (True → ((((False ∧ (p1 → p1)) → p5) → False) → ((False ∧ ((p3 ∨ p1) ∧ (p4 ∧ (p1 ∧ ((p3 → p5) → p3))))) ∧ (p3 → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∧ (p1 → p1)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h7 := h2 h3
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : ((False ∧ (p1 → p1)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h12 := h2 h8
  -- False on the left can always be used.
  apply False.elim h12
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h13 : ((False ∧ (p1 → p1)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h14
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h17 := h2 h13
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h18 : ((False ∧ (p1 → p1)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h19
    -- Conjunctions on the left can always be decomposed.
    let h20 := h19.left
    let h21 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h22 := h2 h18
  -- False on the left can always be used.
  apply False.elim h22
  -- Implications on the right can always be decomposed.
  intro h23
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h24 : ((False ∧ (p1 → p1)) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h25
    -- Conjunctions on the left can always be decomposed.
    let h26 := h25.left
    let h27 := h25.right
    -- False on the left can always be used.
    apply False.elim h26
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h28 := h2 h24
  -- False on the left can always be used.
  apply False.elim h28
  -- Implications on the right can always be decomposed.
  intro h29
  -- One of the premise coincides with the conclusion.
  exact h29



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209516091056036014096054975384 : ((p4 → (((p1 ∧ False) ∨ p4) → p1)) → ((((p5 ∧ ((p1 ∨ p4) ∧ False)) ∨ (((False → False) ∨ False) ∨ (p5 → p5))) → (p2 ∧ False)) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∧ ((p1 ∨ p4) ∧ False)) ∨ (((False → False) ∨ False) ∨ (p5 → p5))) := by
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
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h3
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158857903715981894857999204114 : ((False ∨ ((((p1 ∧ ((p1 ∧ p4) → p3)) → (p2 ∧ (p2 → True))) → ((p4 ∨ p1) ∧ True)) ∨ p1)) ∨ (False → ((p5 ∧ (p2 ∨ p4)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158975325471471771106775807716 : ((p3 ∨ ((p5 ∨ (((p4 ∧ ((False → p5) ∧ True)) ∧ p3) → (p2 ∨ ((p2 → p5) → p3)))) → p1)) ∨ ((p2 ∧ (p2 ∨ p5)) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154255921533715615297715870758 : ((((p1 → (p5 → (p5 → p4))) → ((True → (((True → p5) → (p1 ∨ True)) → p1)) → p3)) ∨ True) ∧ (p2 → (((p2 ∧ p5) → True) ∧ p2))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356751259398633307940726169215 : (p5 → ((((p2 → (p1 → p2)) ∨ p3) ∧ p1) → ((p5 → p2) ∨ (p3 ∨ (p4 ∨ (p3 ∨ ((p5 ∧ (p4 → p5)) ∨ ((p1 ∨ p1) ∧ p4)))))))) := by
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
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658409977609494822788938132530 : ((((False ∨ (p1 ∨ (((p4 → False) ∨ ((((True → ((p3 → p5) ∨ p5)) → p1) → (p3 ∧ p4)) → (False → p5))) ∧ False))) ∨ (p4 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_144551910019221485441312907038 : (((((True → (p4 ∨ (p3 ∨ p5))) → p4) ∨ (p2 → (p4 ∨ (p2 ∨ (p1 ∧ (p3 → True)))))) ∨ (p2 → p5)) ∧ ((p1 → (p4 → p5)) ∨ True)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51366283018502646270017347504 : ((((p5 ∧ (p2 ∧ (((p4 ∧ False) ∨ True) → (False → ((p5 ∨ (p1 ∧ True)) → True))))) ∧ p4) → ((p5 → False) ∨ (True → (True ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324472233155026315319459679233 : (p5 ∨ ((p5 → ((p4 ∨ p3) ∨ p5)) ∧ (p2 ∨ (((p3 ∧ (p2 ∨ ((p2 → p5) ∨ p3))) ∨ (((p3 ∧ p2) ∨ True) ∨ p4)) ∧ (False → p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164435398864692120302304525016 : ((p5 → (p1 ∨ ((p2 ∧ p3) ∨ (p1 → (((p4 ∨ (False ∨ False)) ∨ (p3 ∧ p5)) ∨ p5))))) ∧ ((True ∨ (p5 ∨ True)) ∨ (p1 ∨ (False ∨ False)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739502019932101957936994241800 : ((((p5 ∧ p1) ∨ (((p2 ∧ (p3 ∧ p2)) ∧ (((p4 → p4) → (p4 → p1)) ∨ p1)) → ((False → (p1 ∨ True)) → (p1 ∨ (p3 ∧ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65784153571701377642838468862 : ((p4 ∨ ((p5 ∧ (((p5 ∨ ((p1 ∨ (p4 ∨ (p5 ∨ p4))) ∨ p3)) ∧ p2) ∧ True)) → (((p4 → (p2 → p3)) → (p3 ∨ p3)) ∨ p2))) ∨ p2) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h14 =>
          -- Disjunctions on the left can always be decomposed.
          cases h14
          case inl h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
          case inr h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h7
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42852345867467681641589875284 : (((p2 → (((((p5 → ((p4 ∧ (p3 ∧ ((p1 ∨ p5) ∧ (p2 ∨ p2)))) ∧ p2)) ∨ p5) → p1) ∧ (False → True)) ∨ (True ∧ p2))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624907585151604180440920172743 : ((((p5 ∨ ((False ∧ (p2 ∨ p5)) ∧ (p2 ∨ (p1 → (((((True → (p1 ∨ p5)) ∨ (p1 ∨ p3)) ∧ p4) ∨ (p1 ∨ p4)) ∧ True))))) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159060699532277991123011584455 : ((p5 ∨ ((((p1 → p3) ∨ p5) ∨ p4) → (True → (((p3 ∨ (p2 ∧ (False ∨ p5))) ∨ p5) ∨ p4)))) ∨ ((p5 ∧ p1) → (p5 ∨ (p1 → p3)))) := by
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
theorem thm_5_vars_167957807760260811265007755825 : (((((False ∨ p1) ∨ True) ∧ ((p1 ∨ True) ∨ p5)) → (p5 → (p5 ∨ ((p2 ∧ False) ∨ p4)))) → (((p3 ∨ (p5 → (True ∧ False))) ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47572841448716539620582884310 : (((p1 → ((((p2 ∧ (((p3 ∨ p5) ∨ True) → False)) → p1) → (((p3 ∨ (False ∨ p2)) → (p5 ∧ True)) ∧ False)) ∨ p5)) ∨ (True ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111245482239633686096155497130 : ((((p4 → False) ∧ (((((p2 ∧ p1) ∨ p4) ∨ (((p4 ∨ (False → p2)) ∨ True) ∧ (p4 ∨ p4))) ∨ (p5 ∧ p3)) ∨ True)) ∧ False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_943259271354481695594169658056 : (((((p3 → p1) → (True ∧ False)) ∧ ((((p2 ∧ p2) ∨ (p1 → (p5 ∧ p2))) ∨ (((p4 ∨ False) ∧ p4) ∨ (p1 ∨ p5))) ∧ (True ∧ p1))) → False) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h5.left
      let h11 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : (p3 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- One of the premise coincides with the conclusion.
        exact h11
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h5.left
      let h18 := h5.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : (p3 → p1) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h19
      -- We need to get the right conjuct of h21 based on <expert-advice>.
      let h22 := h21.right
      -- False on the left can always be used.
      apply False.elim h22
  case inr h23 =>
    -- Disjunctions on the left can always be decomposed.
    cases h23
    case inl h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h27 =>
        -- Conjunctions on the left can always be decomposed.
        let h28 := h5.left
        let h29 := h5.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h30 : (p3 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h31
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h32 := h2 h30
        -- We need to get the right conjuct of h32 based on <expert-advice>.
        let h33 := h32.right
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Conjunctions on the left can always be decomposed.
        let h37 := h5.left
        let h38 := h5.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h39 : (p3 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h40
          -- One of the premise coincides with the conclusion.
          exact h38
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h41 := h2 h39
        -- We need to get the right conjuct of h41 based on <expert-advice>.
        let h42 := h41.right
        -- False on the left can always be used.
        apply False.elim h42
      case inr h43 =>
        -- Conjunctions on the left can always be decomposed.
        let h44 := h5.left
        let h45 := h5.right
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h46 : (p3 → p1) := by
          -- Implications on the right can always be decomposed.
          intro h47
          -- One of the premise coincides with the conclusion.
          exact h45
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h48 := h2 h46
        -- We need to get the right conjuct of h48 based on <expert-advice>.
        let h49 := h48.right
        -- False on the left can always be used.
        apply False.elim h49
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322300093585109089036598611901 : (p5 ∨ ((((p5 ∧ (False ∨ True)) → ((((((p3 ∧ ((p3 ∧ p2) ∨ p2)) ∧ (True ∨ p2)) → p5) ∨ (p4 ∧ p2)) ∨ p3) → p5)) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630843502651212945422546144633 : (((((((((p2 ∧ (((p1 → (False → (True ∨ True))) ∧ p4) ∧ p5)) → (p1 → True)) ∨ (False ∧ (False ∨ False))) → p1) ∧ p5) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66787903911478431723978712559 : ((True → (False ∨ (p3 ∧ ((p4 ∧ False) ∨ ((((p3 ∨ p2) → (True ∨ False)) ∧ p3) ∧ ((False → False) ∨ (((False ∧ p2) ∨ p5) ∧ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248291122244105103777329306119 : ((p2 ∨ p2) ∨ ((True ∧ p2) ∨ (p3 → (((p5 → p5) → ((p1 → ((p2 → p2) → (p4 ∧ p3))) ∨ (((p1 → True) → p2) ∧ False))) ∨ p3)))) := by
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
theorem thm_5_vars_264266024694460491867569180832 : (True ∧ ((((p5 → False) → p3) ∧ (p5 ∧ p2)) ∨ ((((True ∧ ((((p5 ∨ False) → p4) → (p3 → p5)) ∨ (p2 → p1))) → p4) ∨ p1) ∨ True))) := by
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
theorem thm_5_vars_257145243152287764307323924943 : ((p2 ∨ p1) → ((((((p1 ∨ p3) → False) ∧ p5) → ((p5 ∧ p1) ∨ p3)) → (p3 ∨ p1)) ∨ (False → (((p2 → False) ∨ (False ∧ p3)) → False)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h7
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178543766323828372087878263545 : (((p5 ∨ (p5 → ((p3 ∨ False) ∧ (p1 → p4)))) → ((p2 ∧ p5) ∧ p1)) ∨ (((p3 ∨ p5) → p5) ∨ ((((True ∨ p1) ∨ False) → p4) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349421869581389906288094786595 : (p3 → (p4 → (((p5 ∨ False) ∧ ((p1 ∧ p2) ∧ p2)) ∨ ((((p2 ∨ (p3 ∨ (p3 ∨ ((False → (True ∧ p4)) ∨ p3)))) ∧ p2) → p5) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191231682219328189587633180005 : (((False → (p4 ∧ p1)) → ((p1 → p2) ∧ (p1 ∧ p5))) ∨ (True ∨ (True ∨ (p5 ∨ (True ∨ (((p2 ∨ (p1 ∧ (p4 ∧ p5))) ∧ p2) ∧ p1)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58890474404881827737786397697 : (((False ∧ p3) ∨ (((p3 → p3) → (p2 ∧ (p2 → ((p5 ∨ p3) ∧ ((p2 ∧ p5) ∧ (False → (p3 → (p3 → True)))))))) ∨ (p2 ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341690373443726645702809580563 : (p2 → ((((((p3 ∧ p2) → p4) ∧ ((((p3 ∧ p3) ∧ p3) ∨ (True ∨ True)) ∧ (p1 ∧ (True ∧ p3)))) ∨ True) ∧ (False → p3)) ∨ (p4 ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591765765507043888302221906772 : ((((((((((p2 ∧ (p2 ∧ False)) → p3) ∧ ((True ∧ p5) → p4)) ∨ ((False ∧ p2) ∧ False)) ∨ p5) ∧ (p2 ∨ p5)) ∨ (p3 ∧ p3)) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125531746517100312122838303171 : (((True → True) ∧ (p2 ∧ (True → ((True ∨ (((p2 ∧ (p2 ∧ (True ∨ p2))) ∧ ((p1 ∧ p4) → False)) ∨ False)) ∧ (p4 ∨ False))))) → (p4 ∧ True)) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350002041440488716137893819086 : (p4 → ((((False → True) → (((p1 → (p1 → (p3 → (p5 ∧ False)))) ∨ ((p3 ∧ (p2 ∧ p2)) ∨ ((p3 ∨ p2) ∧ p4))) → False)) ∨ p4) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_916038263428275702966118772765 : (((((((True ∨ p2) ∨ (True → (p2 ∧ p3))) → False) ∧ ((p4 ∧ p5) → (True ∨ p5))) ∨ (p5 ∧ (False ∨ ((False ∧ (p2 → p4)) ∧ True)))) → p2) ∧ True) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((True ∨ p2) ∨ (True → (p2 ∧ p3))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h12.left
      let h15 := h12.right
      -- False on the left can always be used.
      apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185121184804527495879562325691 : (((True ∧ p4) → (((p4 ∨ (True ∧ p4)) → p3) → (p5 ∧ False))) ∨ ((p3 → (p5 ∨ (p4 ∨ (False ∨ p3)))) ∨ ((p1 ∧ p4) → (False ∨ p5)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312362271083684133289202847255 : (p2 ∨ (p3 → ((((p3 ∧ p4) ∨ (p4 ∨ (p4 ∧ p2))) → ((p4 ∧ ((p2 ∨ p5) ∨ (p5 → (False ∧ p3)))) ∧ (False ∨ p1))) ∨ (p5 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135065875368488194393424113493 : ((((False → (((((p1 → p5) ∧ ((p5 → (p2 ∧ p2)) ∧ False)) ∧ p1) ∧ False) → (p5 ∧ p2))) → p5) ∨ (p1 → p1)) ∨ ((p4 ∧ p2) ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47581121768313957974522411193 : (((p1 → (p5 ∨ ((p5 ∧ (((False → ((((p5 ∨ False) → p1) ∨ True) → p5)) ∨ ((p4 ∨ p4) → False)) ∨ p1)) ∧ p3))) ∨ (p1 ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_737740700184174225830449921322 : ((((p5 → p5) ∧ (False ∧ ((((p3 ∧ True) ∨ p4) ∨ ((False → ((p1 → (p3 → p4)) → (p4 ∧ (p1 ∨ p1)))) → p4)) ∨ (p3 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161550151482304787767779357307 : ((p5 ∧ ((p2 ∨ p2) ∨ ((p3 ∧ p1) ∨ (((p2 ∧ (p4 → True)) → ((False ∧ True) ∨ p5)) ∧ p4)))) → ((p1 ∨ p1) ∨ (p1 ∨ (False → p2)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- False on the left can always be used.
      apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592508797998404142769918597502 : ((((((p4 → p5) ∧ ((((p1 ∧ p1) ∨ (False → (p3 ∨ (p3 ∧ (p3 ∧ p3))))) → ((True ∨ p5) ∧ p2)) → p2)) → (p5 ∨ True)) ∧ True) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301146454435434552334597528237 : (False ∨ ((((False ∨ (p5 → p1)) → p2) ∨ (p1 ∧ p5)) ∨ (True ∧ (((True ∧ (((p3 ∧ True) ∧ p1) ∧ (p2 ∨ False))) ∨ False) → (p4 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312133944280166092691202342622 : (p2 ∨ (True → ((p3 ∧ (True → (p5 ∨ (True → p5)))) ∨ (((p5 → p1) ∨ (False ∨ ((False ∧ (((False ∧ p4) → False) ∧ p2)) → False))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_37743746584055082185563669140 : ((((((p5 → p3) ∧ (((p1 → p4) → False) ∧ p2)) → (p3 → (p2 → (((False ∨ (False ∨ True)) → p4) ∨ (False → p2))))) → p5) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118706120512840696214495524396 : ((p5 ∨ ((((p1 ∧ (p2 → (p3 ∧ p2))) → (p1 → p2)) ∨ (p2 ∧ (((False ∨ (p4 ∨ p4)) ∨ (p3 ∧ p2)) → p2))) → False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68542426498996643041346384215 : ((p3 → (p3 → ((False ∨ ((((p2 ∧ True) ∧ p1) → (p3 ∨ (False → p3))) ∧ (((True ∨ p2) ∨ p4) ∨ True))) → ((False → p3) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621425666111085146270880665976 : ((((True ∧ (p3 → ((((p5 → (p2 ∧ (p4 → p1))) ∨ True) → p5) ∧ ((p3 ∧ ((p1 → p4) → p5)) → (p4 ∨ (p3 → p2)))))) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180555902755149551521581887361 : (((((((True ∧ p4) ∨ p4) ∧ p4) ∧ p5) ∧ p5) → (p1 ∧ (p5 ∧ p4))) → ((p2 ∧ (p5 ∨ True)) → ((p1 ∨ p2) ∨ ((True → p5) ∨ p2)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249920358387882129377054849262 : ((True → p1) ∨ ((False ∨ (p2 ∨ ((True → ((True ∧ False) ∨ False)) → (p5 ∧ p5)))) → (((True → (False → False)) → False) → (p3 ∧ (p1 ∧ p2))))) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (True → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h9 := h2 h6
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (True → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h12
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h14 := h2 h11
      -- False on the left can always be used.
      apply False.elim h14
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h15 =>
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h18 : (True → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h18
      -- False on the left can always be used.
      apply False.elim h21
    case inr h22 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h23 : (True → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h24
        -- Implications on the right can always be decomposed.
        intro h25
        -- False on the left can always be used.
        apply False.elim h25
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h26 := h2 h23
      -- False on the left can always be used.
      apply False.elim h26
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h27 =>
    -- False on the left can always be used.
    apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h29
    case inr h30 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h31 : (True → (False → False)) := by
        -- Implications on the right can always be decomposed.
        intro h32
        -- Implications on the right can always be decomposed.
        intro h33
        -- False on the left can always be used.
        apply False.elim h33
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h34 := h2 h31
      -- False on the left can always be used.
      apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22248924860990663661938910112 : (((p3 → (False ∨ ((p2 ∨ (False ∧ False)) ∨ p2))) ∨ (p4 ∨ (p2 → (((p3 → (False → p4)) ∨ p4) ∧ (p2 ∨ (p1 ∧ (p4 → p4))))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670282948878303221687184273679 : (((((p1 → (p4 ∧ (p3 ∧ True))) → ((p3 → p2) ∧ (((p1 ∨ (p4 → False)) ∧ p3) ∨ ((True → p5) → p5)))) ∨ (False → (p1 → False))) ∨ p3) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_105740856958228533493470224640 : ((((p4 ∧ p4) ∨ ((((p2 ∧ False) → False) → p1) ∧ (True ∨ ((False → p1) ∧ p1)))) ∨ (False ∨ ((True ∨ True) ∨ (p1 ∧ True)))) ∧ (p2 → True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190678411479019304048568617656 : (((p3 → ((p2 → p1) ∧ (p5 → (p5 ∧ p3)))) → False) ∨ (((p1 ∧ (p3 ∧ (p2 ∨ ((True → p5) ∧ p4)))) ∧ (p2 → (False → p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200176968788617608310137068734 : ((((p5 → p5) → p2) ∨ ((p2 ∨ p4) ∨ p2)) → ((p2 ∧ (((((p3 ∧ p3) ∨ True) → True) → p4) → p5)) ∨ (p5 → (p5 ∨ (p2 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68721241446487252714767623444 : ((p4 → (((((((p2 → (p2 ∨ p4)) → p3) → (p5 ∨ ((p4 ∨ False) ∨ (False ∨ p1)))) ∧ p3) ∧ p4) ∨ p4) → (p2 ∧ (p1 ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46268527413575912940546899498 : ((((False → (p5 ∨ (((True ∧ (True ∨ p2)) → (((True ∨ p3) ∧ (p4 ∨ True)) ∨ p3)) ∧ (p4 ∨ True)))) → (True → p5)) ∧ (False ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_96475732561530702560703927363 : ((False ∨ ((p1 ∧ ((p4 → (p1 → True)) ∧ p2)) ∧ (((p5 ∧ ((False ∨ (True → p5)) → p3)) ∨ p2) ∧ (((p3 ∨ p1) ∧ p1) → False)))) → False) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h5.left
    let h11 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h15 : ((p3 ∨ p1) ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h16 := h11 h15
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h18 : ((p3 ∨ p1) ∧ p1) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h19 := h11 h18
      -- False on the left can always be used.
      apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149070210103709024166925616548 : ((((p1 ∨ p4) ∨ True) → (True → (((p2 ∨ (True ∨ (p3 ∨ False))) ∨ p4) → (p4 → (True ∧ (p2 ∧ p2)))))) ∨ (p1 → ((p2 → p4) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674535754854854861138509265808 : ((((p5 ∨ ((p4 ∨ p2) ∨ ((((((True ∨ ((p5 → p5) → p5)) → p1) → p2) ∧ p5) → (p1 ∧ p5)) → p4))) → ((p4 ∨ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_574318249247086549811195366875 : (((p2 → ((((True ∧ ((p3 ∧ (p5 ∨ (p4 ∧ (p1 → (p2 ∨ p3))))) ∨ p5)) ∧ p4) ∨ (p4 ∨ ((p2 ∧ p4) → p2))) ∨ (p2 → p3))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118886361794895349566697945516 : ((True → (p2 ∧ (((False → p5) → ((p3 ∨ p5) ∧ (((p5 ∨ (False ∨ ((True → p1) ∧ False))) ∨ (p1 → p1)) ∨ p1))) ∧ p1))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65509868950078126190383380936 : ((p3 ∨ (False ∨ ((p2 ∧ ((p2 ∧ (((((False ∧ p3) → (True ∨ False)) ∨ (True ∧ p5)) ∧ False) → p1)) → (p2 → p5))) ∧ (False ∧ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122160959598549981349483594043 : (((((p1 ∧ p3) ∨ ((p3 ∨ p4) ∨ (p3 ∧ (((True ∨ True) → (False → p3)) → (p5 ∧ (p4 → p3)))))) → True) ∧ (p3 ∧ p2)) → (p5 ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55921102258642536824094448745 : (((False → ((True ∧ p2) ∨ p1)) ∧ ((p3 → (p1 ∧ (p4 ∧ (p1 ∨ False)))) ∨ (((p1 ∨ True) ∧ (p3 ∨ False)) ∧ (True ∧ (False ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184206016009754945128577073985 : ((((p1 ∨ (((p5 ∧ p5) → (True → False)) ∨ True)) ∧ p2) → False) ∨ ((p3 → p4) ∨ (p5 → (False ∨ (((False ∧ p4) ∨ (p1 ∨ True)) → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_789142572264771912321889283837 : (((p5 ∨ ((p1 ∧ ((p1 ∧ True) ∧ ((p1 ∨ p2) → ((p3 ∧ ((p3 ∧ True) ∨ (p5 ∨ p2))) ∨ (False ∧ p1))))) ∨ ((False → False) ∨ p5))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137516418571657783691062106616 : ((p5 ∧ ((p4 ∧ ((p5 ∧ p1) ∨ False)) → (((p2 ∨ True) → (((p1 ∨ p5) → (p2 ∨ p2)) ∧ False)) ∨ (p3 → p4)))) ∨ (False → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45959726663731295163502868261 : (((p5 → ((p5 ∨ p3) ∧ (p5 ∨ ((p2 ∨ (((p1 ∨ p4) ∧ p4) ∧ p3)) → (((True ∧ p2) ∨ (p4 → (p1 → p3))) ∨ p3))))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171734884030987497293771606702 : (((((p1 ∧ ((p1 → ((p5 ∧ p5) ∧ (p3 ∧ False))) ∨ p2)) ∧ False) ∨ p3) → p1) ∨ (((((p4 ∨ p2) ∨ (p3 → p5)) ∧ False) ∨ True) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355594501505028804237634152280 : (p5 → ((((p2 → False) → (p2 ∨ p4)) ∨ ((p1 ∧ False) ∨ (p2 → (((p2 ∧ p5) ∧ ((p5 ∨ (p2 ∧ p1)) ∨ p4)) ∨ p2)))) ∨ (p3 ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345361617293623566562695656318 : (p3 → ((((p5 ∨ (p3 ∨ (((p2 ∧ ((((p4 → True) → False) ∨ p2) ∨ p1)) → (((p3 → p5) ∨ p3) → True)) → p3))) → False) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62076983323659151205589428316 : ((p2 ∧ (p1 ∧ ((p4 ∧ (True ∨ p4)) ∧ (((False ∨ (p5 → ((False ∨ True) ∧ p2))) → (((p1 ∧ (p2 ∧ p5)) ∧ True) → True)) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234723252308524176013928463429 : ((p4 → (p4 ∨ p1)) → ((p1 → (p5 ∨ p2)) ∨ ((((True ∧ p1) ∨ (p4 → True)) ∨ (p4 ∨ (p1 ∧ ((p4 ∨ (True ∨ p3)) ∧ p2)))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50402427102081269478192145383 : (((True ∧ ((((p4 ∧ p3) ∨ ((p1 → (False ∧ p1)) ∨ (p3 → ((False ∨ p3) ∨ p4)))) → False) ∧ p5)) ∨ (((p2 ∧ True) → p4) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117216391226324673756623514115 : ((True ∧ ((False ∧ (p5 ∨ True)) ∨ ((((p4 ∨ (p4 → (((True ∨ p2) ∨ p2) ∧ p4))) ∧ (p3 ∨ True)) ∨ p2) ∧ (p1 ∧ p4)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186313743039926620669204741864 : (((((p5 ∧ True) ∧ ((p1 → p3) ∨ False)) ∨ (True ∨ False)) → False) → ((((p4 → (True ∧ p2)) ∧ ((p4 → p1) → False)) ∨ False) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53578055454272868168349964348 : ((((p5 → (((p1 ∧ p5) → (False ∨ p4)) → p5)) ∨ p2) ∧ ((p1 → p4) ∨ (((p1 ∧ False) → p1) ∧ (p5 ∨ (p5 ∧ (p5 ∧ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315130130503288527307335296578 : (p3 ∨ ((False ∧ ((p3 ∨ (p4 ∨ p4)) ∨ True)) ∨ ((False ∧ p2) → (((p2 ∨ p3) → (False → (True ∧ (p5 → p1)))) ∧ ((p5 ∨ p5) ∧ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338697416498159711443075804888 : (p1 → ((p3 ∨ p1) ∧ (((((p4 ∨ p3) ∨ ((p2 → ((True ∧ p2) ∨ False)) ∧ (p4 ∧ (p2 ∨ True)))) → p3) ∨ ((True ∨ True) ∨ p2)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182613390878537759904875061076 : (((((False ∨ p1) ∧ p5) ∨ (p2 ∨ p1)) ∨ ((p1 ∨ p2) ∨ True)) ∧ (False ∨ ((((p2 ∧ ((True ∧ p5) ∨ (p2 ∨ False))) ∧ p3) ∨ p2) → True))) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137669389141565288043113681883 : ((False ∨ (p5 ∨ (((True ∨ (p3 ∧ p4)) ∧ True) ∧ ((((p5 ∧ p3) ∨ (True → p4)) → (p3 → (p2 ∨ False))) ∨ p4)))) ∨ (p3 → (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50970380336557683499571805634 : (((((p4 ∧ (p3 ∨ p4)) ∨ p4) → (((True ∧ False) ∨ True) ∧ (((False → p1) → p3) → False))) ∧ ((p1 ∨ (p2 ∨ (p1 → p5))) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39446956996437254390999587904 : (((p5 ∧ (((p3 → False) ∧ (((((True ∧ ((p3 ∧ p5) ∨ p3)) ∨ p4) ∧ p3) ∧ (p3 → p2)) → p5)) → ((p4 → p5) ∨ p5))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246785095963081345418867631718 : ((p5 ∧ p5) ∨ (p3 ∨ (((True ∨ (p4 ∨ ((((p4 ∧ p5) → (p2 ∨ (p3 → (p1 → p1)))) ∨ (False ∨ p1)) → False))) → p5) → (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p4 ∨ ((((p4 ∧ p5) → (p2 ∨ (p3 → (p1 → p1)))) ∨ (False ∨ p1)) → False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90817078507787412650611157351 : (((p3 ∨ p3) ∧ ((((p3 → p4) ∧ (((p4 ∨ ((p1 → p3) → False)) ∨ (((p1 ∧ (p4 → p5)) ∨ False) ∧ p5)) ∧ p2)) ∨ p4) ∧ p3)) → p4) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h15 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h16 := h8 h15
          -- One of the premise coincides with the conclusion.
          exact h16
      case inr h17 =>
        -- Conjunctions on the left can always be decomposed.
        let h18 := h17.left
        let h19 := h17.right
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h20 =>
          -- Conjunctions on the left can always be decomposed.
          let h21 := h20.left
          let h22 := h20.right
          -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
          have h23 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h6
          -- We have shown the premise of h8, we can now drive its conclusion.
          let h24 := h8 h23
          -- One of the premise coincides with the conclusion.
          exact h24
        case inr h25 =>
          -- False on the left can always be used.
          apply False.elim h25
    case inr h26 =>
      -- One of the premise coincides with the conclusion.
      exact h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h3.left
    let h29 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Conjunctions on the left can always be decomposed.
      let h33 := h32.left
      let h34 := h32.right
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h35 =>
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h36 =>
          -- One of the premise coincides with the conclusion.
          exact h36
        case inr h37 =>
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h38 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h39 := h31 h38
          -- One of the premise coincides with the conclusion.
          exact h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h40.left
        let h42 := h40.right
        -- Disjunctions on the left can always be decomposed.
        cases h41
        case inl h43 =>
          -- Conjunctions on the left can always be decomposed.
          let h44 := h43.left
          let h45 := h43.right
          -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
          have h46 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h29
          -- We have shown the premise of h31, we can now drive its conclusion.
          let h47 := h31 h46
          -- One of the premise coincides with the conclusion.
          exact h47
        case inr h48 =>
          -- False on the left can always be used.
          apply False.elim h48
    case inr h49 =>
      -- One of the premise coincides with the conclusion.
      exact h49



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638299791654951682782266849598 : (((((((p4 ∨ p4) ∧ (False → p4)) ∨ p4) ∧ (False ∨ (((((p1 → p1) ∧ True) ∧ p5) → (False ∨ p2)) ∧ (True ∧ (p4 ∧ True))))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



