variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706743189281214525158810983843 : ((((((((False → p1) ∧ p2) ∧ p5) → p4) ∧ p4) ∨ (((True ∧ (((p3 → (p5 ∨ (p5 → False))) ∨ (p4 ∧ False)) ∨ p1)) ∧ p2) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_158408546040954197795356698508 : (((False ∧ p4) ∨ ((p3 ∨ (p5 → (p2 ∧ (((p2 ∧ (p4 ∨ (p5 ∧ p5))) ∨ p5) ∧ False)))) ∨ True)) ∨ ((True ∨ p1) ∨ (False → (p4 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138761929447822755245697322667 : ((((True ∨ (p1 ∨ p2)) → (((p2 ∨ p5) ∧ ((True ∨ p1) ∧ p5)) ∧ (p2 ∧ ((p4 ∨ p2) ∧ (True → p3))))) ∧ p4) → ((p2 ∨ True) → p2)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (p1 ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h10 := h7 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42056778398744039440879046882 : ((((p2 ∨ p5) ∨ ((True → False) ∨ ((p5 ∨ (((p2 ∨ ((p1 ∨ ((True ∧ p4) → False)) → p3)) ∨ p3) ∨ (p4 → False))) ∧ False))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112840436058775596597430115470 : ((((False → ((True ∧ False) → p5)) → (p2 ∧ (((True → p2) ∧ p4) ∨ (((True ∨ p3) ∨ (p4 ∨ (False ∧ False))) → p2)))) → p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590882463915395385555978163462 : (((((p5 ∨ ((True ∧ False) ∨ (((True ∨ False) → (((p4 ∧ (p4 ∧ False)) → p2) → (False ∨ (p5 → (p3 → p4))))) → p3))) → p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172592159840848859866529210152 : ((((False ∨ p1) → True) → (p5 ∧ (((p5 ∧ False) ∨ ((p1 ∧ p1) ∨ True)) → p3))) ∨ (p4 ∨ (((p2 ∧ (p3 ∧ p5)) ∧ p4) → (p4 ∨ p2)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134345181738742025827610289243 : (((p5 ∧ (((p3 ∧ p2) → (True ∨ (((p4 → True) → False) ∧ p4))) ∧ (p1 ∧ (((p2 ∨ True) ∨ p3) ∨ p2)))) ∨ p3) ∨ (p4 ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192681155891074735533028887584 : (((((p1 ∧ (True ∨ p5)) → False) ∧ (p5 → p1)) → p2) → (((p1 ∨ p1) ∨ p1) → ((p2 → (p5 ∧ ((False → p3) ∨ (True ∨ p2)))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305427742769728001795932223633 : (p1 ∨ ((((((p1 → (p2 ∨ (p4 → p5))) ∨ ((True ∧ True) ∨ p1)) ∧ p1) ∨ True) ∨ p4) → (((p1 ∧ p1) → (True → (p2 ∨ p1))) ∨ p3))) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h7
        -- Implications on the right can always be decomposed.
        intro h8
        -- Conjunctions on the left can always be decomposed.
        let h9 := h7.left
        let h10 := h7.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Conjunctions on the left can always be decomposed.
          let h13 := h12.left
          let h14 := h12.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h15
          -- Implications on the right can always be decomposed.
          intro h16
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h20
          -- Implications on the right can always be decomposed.
          intro h21
          -- Conjunctions on the left can always be decomposed.
          let h22 := h20.left
          let h23 := h20.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h23
    case inr h24 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h25
      -- Implications on the right can always be decomposed.
      intro h26
      -- Conjunctions on the left can always be decomposed.
      let h27 := h25.left
      let h28 := h25.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h29 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- Conjunctions on the left can always be decomposed.
    let h32 := h30.left
    let h33 := h30.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51124656896853773717036835131 : (((((p4 ∧ (p4 → p4)) ∨ (False ∧ (p1 ∧ ((False ∧ p2) ∨ ((True ∧ p5) → p1))))) ∨ True) ∨ (((False ∨ p3) ∧ False) ∨ (False ∧ p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216868310386909664532615668386 : (((False ∨ (p2 → p4)) ∧ p3) → (((p5 → (((p4 → (((p1 ∨ (True → p2)) ∨ True) ∨ (p1 ∧ p4))) ∧ p4) ∨ (p3 ∧ False))) ∧ p5) ∨ p3)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316759242167212580781272425968 : (p3 ∨ (True → (((p5 ∨ True) ∨ (False ∧ p2)) → ((((False ∨ True) → (p4 → (False ∨ (p4 → (p4 → False))))) → (p5 ∧ (p1 ∧ p5))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111403418762597968576385138332 : (((p2 ∨ (((((((((False ∨ p5) → p2) ∨ True) ∨ p4) → p4) → (p3 ∨ (p1 ∧ False))) ∨ (p2 ∧ p1)) ∨ p1) → p2)) ∧ p2) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670879869609266290956112472181 : ((((p3 ∧ (((((True → (p1 ∨ True)) → p1) → p2) ∨ (False ∧ (p4 → ((False ∧ p3) ∨ (p2 ∧ p2))))) ∨ p4)) ∨ (p2 ∨ (False → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112145586519712844145069456778 : (((p1 ∧ (((p3 → (p4 ∧ (p4 → False))) → False) ∨ (p5 ∨ (((True → p5) ∧ p4) ∧ ((p1 ∧ False) ∨ (p3 → True)))))) ∨ True) ∨ (p4 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4040311606795863537698058443 : (p2 ∨ ((((p2 → (True → ((False ∧ p4) → (p3 → (p1 ∧ True))))) → False) ∧ (p2 → ((p3 ∨ False) → p2))) → (False ∧ (p1 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p2 → (True → ((False ∧ p4) → (p3 → (p1 ∧ True))))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- False on the left can always be used.
    apply False.elim h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h4
  -- False on the left can always be used.
  apply False.elim h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42297093410384500350789585795 : (((p2 ∧ ((((((p5 ∧ (p3 ∨ (True → True))) → p4) → ((p4 ∧ p2) ∧ (True ∨ p4))) ∨ (p3 ∨ (p4 ∨ p5))) → p1) → p3)) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727978095900786554657218185906 : ((((p3 ∨ (p5 ∧ p4)) ∨ ((p2 ∧ p3) ∨ (((p3 → (True ∧ (((p5 → (p4 → True)) → p1) → p2))) ∧ False) → (False ∧ (p3 ∨ True))))) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350026144416696177318742163840 : (p4 → (((((p2 ∨ p1) → (p4 ∨ (((p2 ∧ ((p1 → False) ∧ (p1 ∧ False))) ∨ (True → p3)) ∨ (p5 ∨ p2)))) ∨ (p5 ∨ False)) → p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200234399768068827838978334565 : ((((p4 ∨ p4) ∨ True) → (p2 ∧ (p2 ∧ p4))) → ((True → p5) → (((((p1 ∨ p5) → (p5 ∧ (p5 ∧ True))) → (p2 ∨ p1)) → p4) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39514040411163992325843861182 : (((False ∨ (((((((p4 ∧ p4) ∧ p1) → (p4 ∨ (False ∨ (p1 → True)))) → (((p3 ∨ True) ∨ False) ∧ p4)) ∨ p2) ∨ p2) ∨ True)) ∧ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2124562236867795507753979529 : (((((p1 ∧ True) ∨ True) → p2) ∧ (p5 → ((True ∧ ((p5 ∧ p1) → p3)) ∨ (p1 → False)))) → ((p4 ∧ True) ∨ ((p4 ∧ p4) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p1 ∧ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168847878918004842735723917812 : ((p3 ∨ ((p2 ∨ p4) → (False ∧ ((((True ∧ False) ∨ True) ∨ (p2 → (p2 ∧ p3))) → True)))) → (((p4 ∧ p4) ∨ p3) ∨ ((p4 → True) ∨ p4))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736929630787029054964693926101 : ((((p3 → True) ∧ ((((p2 → ((p2 ∨ p2) ∧ p4)) → ((((p2 ∧ p2) → False) ∧ p3) ∧ p2)) ∧ (((True ∧ True) → p2) ∧ p2)) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153213301698168285847323780613 : ((True ∨ ((p3 → ((p2 ∧ (p4 → (p1 ∧ p3))) ∧ p2)) ∧ ((True ∧ True) ∨ (((True ∧ p3) ∨ p4) ∧ p5)))) → (p4 ∨ (p4 ∨ (p1 → p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215201163949783415317276680888 : ((True ∧ (p3 ∨ (False ∧ p2))) ∨ ((p5 → p4) → (p5 ∨ ((((False ∨ (p4 → True)) ∨ ((p1 ∧ p1) → (True ∨ p1))) ∨ (False → False)) ∨ p3)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313153211169961621454094343227 : (p3 ∨ (((True ∨ (p2 ∨ (p5 ∨ (p1 → ((True ∨ (p3 ∧ False)) ∨ (p5 ∨ p1)))))) → ((((p3 → True) → p1) ∧ True) ∨ (p5 ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
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
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347368208029195010978652373241 : (p3 → (((((True → False) → (p4 ∧ p1)) ∧ False) ∨ p5) ∨ ((((p3 → p2) ∨ (p4 → (p2 ∨ p2))) → p4) → (True ∧ (True ∧ (p4 ∨ p3)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351732318308644426036769259158 : (p4 → (((((p3 ∧ p3) → True) → p5) ∧ (p3 ∧ ((False ∧ (p4 → p1)) ∧ p2))) ∨ (p1 ∨ (((True ∨ False) → p5) → ((p4 ∨ p5) ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321336050156948932086410944456 : (p4 ∨ (p5 ∨ (False ∨ ((p3 → ((p2 ∧ True) ∨ (True ∧ ((True → (False → (False → p2))) ∨ True)))) ∧ ((((True ∨ p3) → p2) ∨ True) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38325028764168236226135488230 : ((((p5 ∨ ((((True ∧ p5) → p4) ∧ p3) → ((((True ∧ (False ∨ False)) ∨ p4) ∨ True) ∨ p5))) → ((p2 ∨ (p1 ∨ p4)) ∧ p2)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184857504708779313472924147962 : ((((p2 → False) ∧ p3) ∧ ((p3 ∨ (p2 ∧ p5)) → (p1 ∨ p2))) ∨ ((p4 ∧ p3) ∨ (p1 → ((p3 ∧ p4) → (((p3 ∨ False) ∨ p2) ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261661304826861233909721265824 : ((p5 → p5) → (False ∨ (((p3 ∨ ((p1 ∨ p4) ∨ p4)) → ((p4 → ((True ∧ p1) ∨ (p3 ∨ (p1 ∨ (p1 ∧ (p3 → True)))))) → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654584450700012106022718648847 : (((((p5 ∨ ((p3 ∧ ((True ∧ (p3 ∨ (((p5 → (p2 → p3)) ∨ (p1 → p4)) ∧ p1))) ∨ (p2 ∧ False))) ∧ False)) ∨ p4) ∨ (p3 ∨ True)) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_219010369058298514453433232974 : ((p4 ∧ (False → (False ∨ p5))) → (((p5 ∨ ((p1 → p5) → (True ∧ p1))) → ((p2 ∧ p5) ∧ p4)) ∨ (p5 ∨ (p1 → (True ∧ (p4 ∧ p4)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178169691979912483896228453494 : ((((False ∧ p2) → (((True ∨ (True ∧ p3)) ∨ (False → True)) → p5)) → p2) ∨ ((((p5 → ((p4 ∨ (p4 → p3)) ∨ p5)) ∧ True) ∨ p4) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_228852125445528326372380239484 : ((p3 ∨ (p3 → False)) ∨ (p4 ∨ ((p2 ∧ p2) ∨ (p4 → (True ∨ (p5 ∨ (True ∨ ((p3 → (p4 ∧ (p4 ∨ (p5 ∨ p4)))) ∨ (p4 ∧ False))))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304774269034061081308454145125 : (p1 ∨ ((p2 ∨ ((p3 → p3) ∧ ((p5 ∧ ((False → p5) → (p1 → p2))) ∨ (p1 → (((False ∨ p1) → p3) → (p4 → True)))))) ∨ (p5 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136571150630426836766439647909 : ((((p4 ∨ p1) → p1) ∨ (p3 ∨ (True ∧ ((p1 → (((False → p2) ∨ p4) → (p3 ∧ p4))) → (p1 ∧ (p4 ∨ p5)))))) ∨ (p2 → (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186353751414949910812548172932 : (((((p1 → p1) → True) → ((p1 ∨ False) ∨ (p3 → True))) → False) → ((((p4 ∨ p2) → ((p4 → p4) ∧ False)) ∨ p4) ∨ (p4 ∨ (p5 → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180676702964764953005279943346 : (((((True ∨ p5) ∨ p2) ∨ (p4 → p1)) → ((p4 → p2) → (p5 ∧ False))) → ((p2 → (((p5 ∨ (p1 ∧ (p4 ∧ p3))) → p3) → False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : (((True ∨ p5) ∨ p2) ∨ (p4 → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618412075752310092604899484888 : (((((((True ∨ p4) ∨ p5) ∧ p4) → ((True ∧ ((False → (False ∨ True)) → ((p2 → p1) → False))) ∨ (p5 ∨ ((False ∧ p3) ∨ p4)))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_219320486029313620268035932106 : ((p2 ∨ (p1 ∧ (False ∨ False))) → ((False ∨ (((p4 → (p3 ∧ (True → ((True ∨ (p5 ∨ p2)) ∧ p1)))) ∧ p3) → p5)) ∨ ((False ∧ True) → p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48979815994573344182740254554 : ((((((((False ∨ (p1 ∨ p5)) ∧ (True ∧ p4)) ∧ p1) → p2) ∨ ((p4 → p5) → ((True ∧ False) ∧ p1))) ∨ True) ∨ ((False → True) ∧ p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259979750073634438487655878479 : ((p2 → True) → (((((((True ∧ p4) → False) → p4) → p2) ∨ False) ∨ ((p1 ∧ (p2 → False)) ∨ (((p5 ∧ (p2 ∧ p1)) → p5) ∨ p2))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65332168237112280161161196840 : ((p3 ∨ ((((True ∧ (False ∧ (p2 ∨ p3))) → ((p4 ∨ False) → (p1 ∨ True))) ∧ ((p5 ∧ p2) ∧ p2)) ∨ (p3 → ((False → p4) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147553439599383551943607286157 : (((p5 → ((p3 ∧ p4) ∨ ((p5 → True) ∧ (((p2 ∨ (p2 ∧ ((p2 → p4) ∨ True))) ∧ p1) ∨ p3)))) ∨ True) ∨ ((False ∧ (p5 → p5)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701808498741436704903957522690 : ((((p3 ∧ (p5 ∧ (p1 ∨ (p4 ∧ ((p4 ∨ p5) → p4))))) ∧ ((((p3 ∧ p3) → ((p4 ∧ (True ∨ True)) ∨ (p2 → p5))) → p2) → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621488608896278044748124232459 : ((((False ∧ (((p3 → ((((p4 ∨ (True ∧ (p3 → p1))) ∨ p2) → ((p2 → p4) ∧ (False ∨ False))) ∧ (p1 ∨ False))) ∧ p5) → p1)) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_261512923031172783473667792723 : ((p5 → p3) → (((((p5 → (p4 ∨ p3)) → ((((p1 → p2) ∧ p1) ∧ False) ∧ (p5 ∨ True))) ∧ (False → p3)) ∨ False) → ((p1 → p2) ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : (p5 → (p4 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h9 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h10 := h1 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h7
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h14
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
    have h18 : (p5 → (p4 ∨ p3)) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h20 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h19
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h21 := h1 h20
      -- One of the premise coincides with the conclusion.
      exact h21
    -- We have shown the premise of h16, we can now drive its conclusion.
    let h22 := h16 h18
    -- We need to get the left conjuct of h22 based on <expert-advice>.
    let h23 := h22.left
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- False on the left can always be used.
    apply False.elim h24
  case inr h25 =>
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183910727987382479211656322895 : ((((p5 → True) → ((p2 ∨ ((p2 ∧ p5) ∨ p4)) → p3)) ∧ p1) ∨ (p1 ∨ ((((False ∨ ((False ∧ p4) → p3)) ∨ p5) ∧ True) → (True ∨ p1)))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615687480277861936210686001463 : (((((((p3 ∨ p3) ∧ ((False ∧ p1) → (p5 → p2))) ∨ (False ∧ (p4 ∧ p2))) ∧ (p5 → (True ∧ (((p1 ∧ p1) ∨ p1) ∧ p5)))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_197039327690300015227477775953 : ((((p2 ∧ p1) ∧ ((False ∧ False) ∧ p5)) ∨ p1) ∨ (((False ∨ (False ∧ (p5 ∨ (p4 ∨ p2)))) → ((False ∧ ((p1 → p5) → True)) → True)) ∨ p4)) := by
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
theorem thm_5_vars_326122348056761538498079854580 : (p5 ∨ (p1 → ((((p5 ∨ (p1 → (p1 ∨ True))) ∧ p1) ∨ p1) ∧ ((p1 ∧ p3) ∨ (((p1 → (((p4 → p2) ∨ p1) ∧ True)) → False) ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178399558770167651185433049895 : ((((p4 → (p1 ∨ False)) ∨ (p2 ∨ ((p5 → True) ∧ p2))) → (True → p5)) ∨ (((p3 ∨ (True → (p1 ∧ (True ∧ p3)))) ∨ p2) ∨ (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178734951437944420297261550049 : ((((p2 → p1) → (p3 ∧ p3)) → (((p3 ∨ p3) ∨ (p1 ∧ p5)) ∨ p5)) ∨ (((p2 ∧ p2) ∧ (True → p5)) → (((p2 → p2) ∧ True) ∨ p2))) := by
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
theorem thm_5_vars_37202885812085412423382216517 : (((((True ∧ (p4 → (p5 ∨ True))) ∧ ((False ∨ p1) ∧ (((p3 ∧ (p3 → True)) ∧ (p2 ∧ p3)) ∧ ((p5 ∨ True) → True)))) ∧ p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_83352555289515559204693821995 : ((((p5 ∨ p2) ∧ (p5 → (((p4 ∨ ((p3 ∨ ((p3 ∨ p5) ∨ False)) → p4)) ∨ p4) ∧ False))) ∧ ((True ∨ (False → (p2 ∧ False))) → p5)) → p2) := by
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
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h7 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138541412382615316307616207263 : (((((p4 ∨ p1) ∧ (p5 ∧ (p2 ∧ (p3 ∨ (((p1 → (p1 ∧ (p1 → p5))) → (p1 ∧ p2)) ∧ p4))))) ∨ p2) ∧ p2) → ((False ∨ p2) ∨ p4)) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h6.left
      let h18 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
  case inr h25 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114128338525555836480190954863 : (((p4 → (((False ∨ (p5 → p4)) → (p2 ∧ (True → ((p3 ∧ (p1 ∧ p5)) ∨ (p2 ∧ p1))))) ∨ True)) ∨ (p3 ∨ (p4 ∧ p4))) ∨ (True → p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56620227336324958501951307587 : ((((p1 ∧ p1) ∧ p3) ∧ (((False ∨ (False → p1)) ∧ (True → ((False ∨ (p4 → (p2 → ((p1 → False) → p1)))) ∧ p1))) ∧ (True ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164765602938117866203420487374 : (((((p2 ∨ p2) → (p4 ∨ (((p4 ∨ False) → False) ∧ p3))) → (p2 ∨ (True ∧ False))) ∨ p5) ∨ ((p5 ∧ (p4 → p2)) → (p5 → (p5 ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725189926472677060679854578141 : ((((p2 → (p2 ∧ p5)) ∧ ((p4 → (p1 ∨ (p2 ∧ (p1 ∧ (p4 → ((p1 ∨ p1) ∨ (p1 ∨ ((p3 ∧ (p3 ∨ p4)) ∧ p3)))))))) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715889049667209178820532364304 : (((((True ∨ (p4 ∨ False)) ∨ p2) ∧ (p5 ∧ ((p5 → ((p1 ∧ (((True ∨ p3) → (p3 ∧ (p2 → False))) ∨ p5)) ∨ (p5 → p5))) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148723232107430952911874453536 : (((False ∨ (p3 ∧ ((p4 → (p3 → p3)) ∨ p3))) → (p2 → (((False → (p4 ∧ (p5 → False))) → p5) ∨ p2))) ∨ ((p2 ∧ (p1 ∨ False)) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685343730532623330224528808819 : ((((p4 → (((((p4 → p5) ∧ p3) → ((p4 ∨ p1) ∨ (p2 ∨ p4))) ∧ p1) ∨ (p4 ∧ False))) ∨ ((False → p1) ∨ (p4 → (p3 ∨ p5)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218977771596537648220467422425 : ((p4 ∧ ((p4 ∧ False) → False)) → (((((True → ((p2 ∧ (p1 ∨ (p4 ∨ (p3 → p1)))) ∧ p5)) → (p1 ∧ (p5 → p4))) → p1) ∨ True) ∧ True)) := by
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
theorem thm_5_vars_863617798313096335729355065693 : (((((((((p3 → False) → p1) ∧ p4) ∨ ((False ∨ p2) ∧ p1)) ∨ True) ∨ ((((p4 ∨ (False → p1)) ∧ p1) ∧ (True ∧ p5)) → p1)) → p4) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p3 → False) → p1) ∧ p4) ∨ ((False ∨ p2) ∧ p1)) ∨ True) ∨ ((((p4 ∨ (False → p1)) ∧ p1) ∧ (True ∧ p5)) → p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116503930178975627722840597682 : (((p3 ∧ p5) ∧ (p5 ∨ (p5 → ((((False ∧ (p1 ∨ (p3 ∨ False))) → (p4 → ((False ∧ (False ∧ p4)) ∧ False))) ∨ p4) → p4)))) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226254247599688101494897063692 : (((p3 ∨ p3) ∨ False) ∨ (p4 ∨ (p2 → (p4 ∨ ((True ∧ ((((p5 → (p1 ∧ p1)) → (True ∧ True)) ∨ True) ∨ p4)) ∨ ((p1 ∧ p3) → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111380005051886608845795700608 : (((False ∨ ((p5 ∧ (p1 ∧ (p2 ∧ (False ∨ (((p5 ∨ True) ∨ ((p2 ∨ True) ∧ p3)) → (True → (False → False))))))) ∧ p1)) ∧ True) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258782823594516423722553124829 : ((True → False) → (((p5 → ((False ∨ p1) ∧ (False ∧ ((True → (p4 ∧ p3)) ∨ (p5 ∧ p5))))) ∧ True) ∧ (p1 ∧ (p3 ∧ (p4 ∧ (p2 ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h7
  -- False on the left can always be used.
  apply False.elim h8
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h11 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h11
  -- False on the left can always be used.
  apply False.elim h12
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h13 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h14 := h1 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_621044590364036522841971482599 : (((((p1 → p2) → (p3 ∧ ((False ∧ ((((((p2 → p5) ∨ False) ∨ p1) ∧ p1) → False) ∨ (False → (p1 ∨ (p2 ∧ False))))) ∨ p1))) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_57736109831674748250397914335 : ((((p4 ∨ True) → p4) → ((True → p1) → ((((p4 ∨ ((p3 → p4) ∨ (True ∧ p4))) ∨ (p4 ∧ p1)) → (p5 ∧ (True ∧ True))) → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118329724318216341183469571369 : ((p2 ∨ ((((True → ((p2 ∨ p4) ∨ p1)) → (p2 → False)) ∧ ((True ∨ False) ∧ (p3 ∨ ((False → (p5 ∧ True)) → p5)))) ∧ p5)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119149476957011409701661123119 : ((p1 → (p5 → ((True → ((True → ((p2 ∨ ((((p5 ∧ p3) ∧ p3) → ((False ∧ p5) ∨ True)) ∧ p1)) ∧ p1)) → False)) ∨ p3))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341095005409695233304084403199 : (p2 → ((p2 → ((p5 ∨ p5) ∨ ((p2 → p5) ∧ ((False ∨ p2) → (((p3 → ((p2 ∨ False) ∧ p2)) ∨ (p1 → (p4 ∨ p4))) → p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115425673589902808647156052600 : (((((p2 ∨ (p1 → False)) ∧ (p3 → p2)) ∨ p5) ∨ (((p3 ∨ p2) ∧ ((((True → p3) ∨ p5) → True) ∨ p5)) → (p3 → p5))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137844277192432477015505195702 : ((p3 ∨ ((p3 ∨ (p4 ∨ (True → (True → p3)))) ∨ (p5 ∨ (True → (p3 ∧ (((p4 ∧ (p3 → False)) ∧ True) ∧ p1)))))) ∨ (False → (p4 ∧ p4))) := by
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
theorem thm_5_vars_117141219413839248310566562513 : (((p5 → p4) → ((p3 ∧ p1) ∨ ((((p4 ∨ ((p1 → p5) ∨ (p2 ∧ p2))) → ((p3 ∨ False) → True)) ∧ (p3 → False)) → p3))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190676458363271674778601604729 : (((p2 → (p5 → (True → (False ∨ (p4 → p5))))) → p4) ∨ ((True ∧ p5) → (p4 ∨ ((True ∨ False) ∧ ((p4 ∨ p3) ∨ ((p5 ∧ True) ∧ True)))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354112106542583628084939907315 : (p4 → (p5 → ((False → True) ∧ ((((False ∨ (((p4 ∨ (((p1 ∧ (p2 ∨ False)) → p4) → p3)) ∨ p1) ∨ (p2 ∧ False))) ∨ p3) → p1) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157948130661432540260253380152 : (((p5 ∨ (p1 ∧ ((p1 ∨ p3) ∧ (p5 ∨ True)))) ∧ (p2 → (p1 → (((p1 → p3) ∨ p3) ∨ p2)))) ∨ (((p3 ∧ False) → p5) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262141640836748812165895577142 : (True ∧ (((((p4 → (((True ∧ p1) ∧ p3) → (False ∧ False))) ∧ ((p4 ∧ (True → ((p1 ∧ p4) ∧ (p3 ∨ p2)))) ∧ p2)) ∨ p4) ∨ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721267341156691801265426094084 : (((((p4 ∨ p3) → (p4 ∧ p4)) → ((((True → p3) → p3) → p2) ∧ ((p3 → (((p1 ∧ (p2 ∧ True)) ∨ p1) ∨ (p2 ∨ p2))) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137021299523984864583915099430 : (((p3 ∨ p2) → (((True ∨ True) ∧ (((p5 ∧ False) → ((p2 ∧ ((p5 → p3) ∧ p5)) ∧ (True ∨ False))) → p1)) ∧ False)) ∨ ((p2 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610212166326924137145029941276 : (((((((p3 ∧ ((p2 ∨ p3) → ((p3 ∨ False) ∧ ((False ∧ (p3 ∨ p3)) ∧ ((p1 → True) ∧ p3))))) ∨ (p4 → False)) ∨ True) → p1) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_37101337492995059841537551620 : (((((((p1 ∨ p2) ∧ (True ∨ (((p3 ∧ p1) ∨ (p4 ∨ (p2 ∧ True))) ∨ (p3 ∧ ((p2 ∧ False) → p3))))) ∨ p4) → p3) ∧ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133612912749277562744898725108 : (((((False ∧ (((True ∧ (p3 ∨ True)) ∧ (False ∨ (p2 ∨ p3))) ∨ (p3 ∧ (False ∧ False)))) → (p4 ∧ p4)) → False) ∧ p4) ∨ ((False ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192185198237908534717639509439 : (((((True ∧ (p3 ∧ p3)) → (p2 → p5)) ∨ p1) ∧ p1) → (p4 → ((p2 ∨ (((True → (p1 → False)) ∧ ((p4 ∨ p4) → p4)) ∨ p1)) ∨ True))) := by
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
theorem thm_5_vars_151675635920828764396695916974 : (((p3 ∧ (((p4 ∨ (p2 → True)) → False) ∧ (p1 ∨ (((p5 → p3) ∨ p2) ∨ p2)))) ∧ ((p2 ∨ p3) → p5)) → (p1 ∨ ((p2 ∧ p1) ∨ p2))) := by
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
  cases h7
  case inl h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
        have h12 : (p4 ∨ (p2 → True)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h6, we can now drive its conclusion.
        let h14 := h6 h12
        -- False on the left can always be used.
        apply False.elim h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316730601977371803903689682171 : (p3 ∨ (True → (((((((p4 ∧ p1) ∨ (p3 → ((p2 ∧ False) → (True ∧ p1)))) → p4) → (True → (p3 ∧ p4))) ∨ p2) → (p1 ∧ p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112924799987817409286508418878 : ((((p1 ∧ p1) → (((p5 → (True ∧ (p2 ∧ (p5 ∨ (p1 ∨ True))))) → ((p4 ∧ False) ∧ ((p2 → True) ∨ p4))) → True)) → p5) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777789878964930533024442912898 : (((p1 ∨ ((True ∧ ((p1 → False) → (p3 ∧ p3))) → (p5 ∨ (((False ∨ p1) ∧ p3) ∧ (((p4 → p1) ∧ p5) ∨ ((p4 → p5) ∨ p4)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739177659811171583962663013401 : ((((p4 ∧ False) ∨ (((p4 ∧ (p1 ∨ p4)) ∨ ((((p4 → p2) ∨ ((((p4 → (True ∧ p1)) → p3) ∨ p4) ∧ p4)) ∧ True) → p3)) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38310220191368578797678523938 : (((((p4 ∧ ((p3 ∨ True) ∨ ((False → p2) ∧ ((p5 ∧ p3) → False)))) → ((p5 ∧ p1) ∧ p2)) → (p2 ∧ (False → (p4 ∨ False)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171652905000128596894495971206 : (((False ∧ ((p3 ∨ (p2 ∧ ((((p2 ∨ p5) ∧ p1) ∨ p1) ∨ p5))) ∨ p3)) ∨ p1) ∨ ((False → ((True ∨ p2) ∧ p1)) → ((p3 ∧ True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336249301623764181617272095146 : (p1 → ((((p3 ∧ ((p2 ∨ (((p4 ∧ p3) ∧ (p1 ∧ (p3 ∧ p1))) ∨ p5)) → p3)) ∨ p4) ∧ (p4 ∨ (p2 ∧ (p3 → (p3 → p4))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_926950258922465067830639065106 : ((((True ∨ (p1 ∧ (True → ((p1 ∧ p3) ∧ ((p4 ∨ True) ∨ p5))))) → (((True ∧ ((p5 ∧ (p4 → (p5 → p3))) ∧ p5)) ∨ p2) ∧ p1)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p1 ∧ (True → ((p1 ∧ p3) ∧ ((p4 ∨ True) ∨ p5))))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



