variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157924989696954794719093927817 : ((((((p5 ∧ p3) → p1) ∧ (True ∧ p4)) ∧ p1) ∧ ((p2 ∨ True) → (((True → p3) ∧ p2) ∧ False))) ∨ (True → (False → ((False ∧ False) → p4)))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198277260402916695289022530042 : ((False ∧ (False ∧ (False ∨ ((False ∨ False) ∧ p2)))) ∨ (((p5 ∨ p1) → False) → ((((p2 → p1) ∧ ((p2 ∨ False) ∧ p4)) → p5) ∨ (True → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h8 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h9 := h3 h8
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h10 : (p5 ∨ p1) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135728277822223679669270000669 : (((((True ∧ (((p3 ∨ (True → p3)) ∧ p3) → p5)) ∨ (p1 ∧ p2)) ∨ p1) ∨ (((p2 ∨ p4) ∨ (p5 ∧ False)) ∧ p3)) ∨ (True ∨ (p2 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_611032209225010988397691871337 : (((((((p1 ∨ (p4 → p2)) → (p3 ∨ p5)) ∨ (p5 → (((True ∧ (p4 ∧ (True → p4))) → p5) ∨ (p3 ∨ (True ∧ True))))) → p1) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215105121148197714348105322764 : (((p1 → p5) → (False ∧ p2)) ∨ (True ∧ (((p2 ∧ p1) ∧ ((False → p4) ∧ ((False ∨ p2) ∨ p4))) ∨ ((p5 ∨ ((p2 → p2) ∧ True)) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318687078156838040546645175400 : (p4 ∨ (((((p3 → ((p3 → p3) ∨ ((p1 ∧ p1) → False))) → False) ∨ ((p1 → ((True → False) ∧ p4)) → (p5 ∨ True))) → p3) → (p3 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → ((p3 → p3) ∨ ((p1 ∧ p1) → False))) → False) ∨ ((p1 → ((True → False) ∧ p4)) → (p5 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54843850092833879250904347282 : (((p5 → ((p1 ∧ p1) ∨ (p2 ∧ (True ∨ False)))) → (p1 → (p5 → ((((False ∨ ((True → p3) ∧ (p4 ∧ False))) ∨ p4) ∨ p2) ∨ p1)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147875615326264027144371330559 : (((p4 → (((p5 ∧ (p5 ∧ p3)) → p1) → (False ∧ (((p4 → False) → True) → (True ∨ (p2 ∨ False)))))) → False) ∨ (False ∨ (p2 ∨ (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263078773248895700258048823610 : (True ∧ (((((p3 → (p1 ∨ True)) ∨ (((((True ∨ p3) ∨ p1) ∧ p2) → p3) ∨ (((False → True) ∨ p2) → p5))) → p1) ∨ True) ∨ (False ∧ p1))) := by
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
theorem thm_5_vars_114808160496220264748475641204 : (((((p3 → p2) ∧ p5) ∨ (((p3 ∨ p1) → (p1 ∧ False)) ∧ (p2 → False))) ∧ (p4 → ((p1 → p3) → ((True ∧ p2) → True)))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213307310840064409972108802622 : (((True ∧ (False → p3)) ∧ p3) ∨ (p3 → (((p2 ∨ ((((((False ∧ False) → False) ∨ p2) → p4) → p2) → p3)) ∧ (p1 → True)) ∧ (False → p1)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200245742292339329038342156301 : ((((p2 ∨ p4) → p5) → ((p4 ∧ False) → False)) → (((True → (p3 ∧ p5)) → (((p2 ∧ p4) ∧ (p3 ∧ (True ∧ p3))) ∧ p2)) ∨ (True ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63977661061116566514537755899 : ((False ∨ ((((p3 ∧ (p5 ∨ ((p2 → p1) ∨ True))) → ((p2 ∧ (p1 ∨ p4)) ∧ False)) → (p4 → (((p2 ∨ p2) ∨ p2) → p5))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683743730927254597859585729396 : ((((((False ∧ ((((p2 ∨ (p3 ∧ False)) ∧ p2) ∨ (p2 ∨ p1)) ∧ (p4 ∧ p4))) ∧ p4) ∨ p3) ∨ ((True → (p2 → (p2 → True))) ∧ True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232726822517655839832695254487 : ((p1 ∧ (True → p1)) → (((((p2 ∧ p4) ∧ True) ∧ p4) ∧ ((((p3 ∧ p1) ∨ (True ∨ p3)) ∨ ((True ∧ p3) ∧ p2)) ∨ p4)) → (p5 ∨ True))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h13.left
        let h15 := h13.right
        -- Conjunctions on the left can always be decomposed.
        let h16 := h1.left
        let h17 := h1.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h18 =>
        -- Disjunctions on the left can always be decomposed.
        cases h18
        case inl h19 =>
          -- Conjunctions on the left can always be decomposed.
          let h20 := h1.left
          let h21 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h1.left
          let h24 := h1.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h25 =>
      -- Conjunctions on the left can always be decomposed.
      let h26 := h25.left
      let h27 := h25.right
      -- Conjunctions on the left can always be decomposed.
      let h28 := h26.left
      let h29 := h26.right
      -- Conjunctions on the left can always be decomposed.
      let h30 := h1.left
      let h31 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h32 =>
    -- Conjunctions on the left can always be decomposed.
    let h33 := h1.left
    let h34 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117489996091998934732482774856 : ((p1 ∧ (p1 → (((((p5 ∨ ((p3 ∧ True) ∨ (p5 → (((p5 → p1) ∨ False) ∨ False)))) ∧ (p3 ∨ p4)) ∧ p5) ∧ p5) → False))) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115937851258278093142187754216 : (((p5 ∧ (p5 ∨ (False → p5))) ∨ (((p5 ∨ False) ∨ ((p2 ∧ p1) ∧ (True ∧ ((True ∨ ((p2 ∨ p1) ∧ p1)) → p2)))) ∧ p4)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134720210322540741605912447232 : ((((p2 ∧ (True ∨ False)) ∨ ((p3 ∧ p3) ∧ ((p4 ∨ (((p2 → ((True → p1) → p3)) ∧ p1) ∧ p4)) ∧ p1))) → False) ∨ (p5 → (p5 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175394534810693128817628639001 : ((True → (False → (True ∧ (((p5 → p3) ∨ p3) → (True ∧ (p5 → (p1 ∧ p1))))))) → ((((p4 → p4) → (p3 ∧ False)) ∧ p2) → (p1 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h5
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149155505420658958848866042850 : (((p1 ∨ p5) ∧ (p1 ∨ (((p4 ∧ (p2 ∨ ((((p3 → False) ∨ p3) ∨ (p2 ∧ True)) → p4))) ∧ p4) → p2))) ∨ (p1 → ((p1 ∨ False) ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_914309044553018639274467221805 : (((((((False ∨ (p4 ∨ ((p4 → p3) ∧ (p4 ∨ True)))) ∨ p2) ∧ True) → (p1 ∧ p5)) ∧ (((p4 ∧ p5) ∨ p4) ∧ (False → (p3 ∧ False)))) → p1) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : (((False ∨ (p4 ∨ ((p4 → p3) ∧ (p4 ∨ True)))) ∨ p2) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h13 : (((False ∨ (p4 ∨ ((p4 → p3) ∧ (p4 ∨ True)))) ∨ p2) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h14 := h2 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- One of the premise coincides with the conclusion.
    exact h15
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328713498909758685274898670363 : (True → ((p3 ∧ (False ∨ ((((p2 ∨ (p5 ∨ False)) ∨ p5) ∨ p1) ∨ p3))) ∨ (True ∨ ((p2 ∨ p4) ∧ (((p2 ∧ (p5 ∧ False)) ∧ p5) ∨ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339511460267956674797177190667 : (p1 → (False ∨ (((False ∧ False) ∨ p5) ∨ ((True → (((p1 ∧ p2) ∨ p5) ∧ False)) → (((p5 ∨ ((p3 ∨ p4) → False)) → (p4 ∧ p1)) ∨ p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168156416535204501005750847615 : ((((p5 ∧ p3) ∨ p2) ∧ (p3 → (p5 ∨ ((False → ((p4 → (p3 ∧ p2)) ∨ p1)) → p5)))) → (((p1 ∨ (p4 ∨ p5)) ∧ p1) ∨ (p5 → True))) := by
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
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190672052057573567634176560708 : (((p1 → (True ∨ (p4 ∨ (p4 ∧ (p4 ∨ p2))))) → p2) ∨ (p2 ∨ ((False → ((p3 ∧ p2) → ((p3 ∨ ((True ∧ p5) ∧ False)) ∧ p4))) ∨ p2))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709741917320411436844974150315 : ((((False → (((p4 ∧ p1) ∨ p2) → (p3 → False))) → ((((p1 ∧ (True ∧ ((True → p1) ∧ (p1 → (p4 ∨ p4))))) ∨ p1) ∨ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318579106408270289364813310935 : (p4 ∨ (((((False ∨ False) ∨ (False ∧ (p5 ∨ ((p2 → (True → False)) ∧ True)))) ∧ (((p5 ∧ p3) → p4) → p3)) ∨ (True → False)) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171945958941088308463679058435 : (((((((True ∧ False) ∧ p4) ∨ (p4 ∨ p2)) ∧ p3) → (True ∧ p1)) ∧ (True ∧ False)) ∨ (((p2 → p1) → (p3 ∧ False)) ∨ ((False → p2) ∨ p1))) := by
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
theorem thm_5_vars_353412308730307535699162210262 : (p4 → (p1 ∨ (((True ∨ (((p5 ∧ (p1 ∨ (p5 → p3))) → True) → p5)) → ((p2 → p2) ∧ (p3 ∨ (p3 ∨ ((p4 ∨ p4) → p5))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56615932274678132948779813584 : ((((False ∧ False) ∧ p2) ∧ (((((True → p5) → ((((p5 → p4) ∧ p1) ∨ (p4 ∧ (p5 ∧ p4))) ∨ p4)) ∧ (True ∧ False)) ∨ True) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647819764946997815782428606767 : ((((((p3 ∨ (((p3 → (((False ∨ (p4 → p3)) → p5) → p1)) → ((p5 ∧ (p3 ∨ False)) → p3)) ∧ p3)) ∧ False) ∧ False) ∧ (False ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322614255607731315696295283527 : (p5 ∨ ((p4 → ((p5 → False) → (p1 ∨ (p5 → (((p1 ∧ p4) ∧ ((p5 → ((True ∧ p2) → ((p5 ∧ p1) → p5))) → p2)) ∨ True))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57080378442481538647358756972 : ((((False ∧ p3) ∧ p1) ∨ ((p5 ∧ p2) → (True → (False ∨ ((p5 ∧ ((p1 → p5) → p3)) ∨ ((((p2 ∧ p4) → p4) ∧ p5) ∨ p4)))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190135162073084488488522753374 : ((((p3 ∨ p4) ∧ (True → (True → (False ∨ False)))) ∧ False) ∨ (p1 → (p3 ∨ ((True → ((p5 ∨ True) ∧ ((True ∧ (p5 → p1)) ∨ p2))) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336212451694522814141049322257 : (p1 → ((((p2 → (p5 ∨ p4)) ∨ (((((((False → p4) ∧ ((False → p2) ∧ p3)) ∧ p2) → p5) → p5) ∧ False) ∨ p4)) → (p2 ∧ True)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114042418830718573973230694024 : (((((p5 ∧ (((((False ∨ True) → p1) ∨ (p1 ∨ p2)) ∧ (False ∨ p1)) → p4)) ∨ False) ∨ (False ∨ False)) ∨ ((p1 → True) ∨ True)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327053031825363342190507962342 : (True → (((p2 ∧ ((p5 ∧ True) ∨ (p3 ∨ p1))) ∧ (p5 ∧ ((p1 → ((p2 ∨ p4) ∨ p3)) → ((p3 ∧ p4) ∧ (False ∧ (p2 ∨ p3)))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38784394634524543971981099680 : (((((True → p1) ∧ (False ∨ False)) ∨ ((((False ∨ p2) ∨ True) ∧ p4) ∨ (((p2 ∨ p1) ∨ (p5 ∧ ((p4 ∨ p2) → p2))) ∨ p1))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165051511599767536454516593197 : ((((False ∨ p5) → ((p5 → (p4 → ((False ∧ (p4 ∧ (p2 ∧ p5))) ∨ p3))) ∨ p3)) → False) ∨ (((p5 → True) ∧ False) → (p2 → (p1 → p3)))) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165378883540435632669533238413 : ((((p5 ∨ (p5 ∨ ((p5 → (p2 ∧ p4)) → p4))) → (False ∧ p2)) ∨ (False ∧ (p5 → p5))) ∨ ((p3 → True) ∨ (p3 ∨ ((p2 ∧ p5) → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111505475254314540822636119081 : (((p4 → (((False ∨ p2) ∨ (False ∨ (p5 ∧ (False ∧ (p4 → (p2 → p2)))))) ∨ (True → ((p1 ∨ (p4 ∨ p1)) → p4)))) ∧ p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136898542013504073809907977173 : (((p4 ∨ p4) ∨ ((((False ∧ (((p5 → p3) → p1) → True)) ∨ (p5 → (((p4 ∧ True) ∨ p5) ∧ True))) → p4) ∨ True)) ∨ (True → (p5 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229056746442363676321369601232 : ((p5 ∨ (p4 ∨ p3)) ∨ (((p1 ∧ p3) ∨ p2) ∨ (p3 ∨ ((True ∨ ((p5 ∧ p4) ∧ p3)) ∨ (((p4 ∧ (p2 → (False ∧ p3))) ∧ p3) ∨ p4))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679375967444599473932225090273 : ((((p4 → (((p5 ∧ (((True ∨ p4) ∨ p1) → p1)) ∧ (p1 ∨ (((p4 ∧ True) → p1) ∧ p1))) ∨ False)) ∨ (((True → False) ∨ p3) → True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40527599097136775030689624958 : ((((False ∨ ((p1 → p5) → (((p2 → ((p3 ∧ (((p5 ∨ ((p2 ∨ p2) ∨ p4)) → p4) → p1)) ∧ True)) → p3) → False))) ∨ p2) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314283946005356738142860372175 : (p3 ∨ ((p2 → (((p3 ∧ p5) ∨ True) ∧ ((p4 ∨ (((p5 → p2) → ((p3 ∧ True) ∨ False)) ∨ (True ∨ p1))) ∨ p3))) ∨ (p1 ∨ (True ∨ False)))) := by
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
theorem thm_5_vars_320376594396983380539622597878 : (p4 ∨ ((p5 → p4) ∨ (((((p5 ∨ (p5 ∧ (p3 ∧ ((True ∨ p5) → p3)))) ∨ p2) ∨ True) → False) → (((True ∧ True) → (p1 ∨ p3)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p5 ∨ (p5 ∧ (p3 ∧ ((True ∨ p5) → p3)))) ∨ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115794186921212068209666126870 : (((((p5 ∨ p5) → p4) ∨ p5) ∧ ((False ∨ p5) → (((p4 ∨ (((p3 → (p5 ∨ p2)) ∧ False) ∧ (p1 → True))) → p4) → False))) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158328346411637346261202763559 : (((True ∧ p2) ∧ (((False ∨ (p2 → p4)) ∧ p1) ∧ (((True → p2) ∨ p4) ∧ (p1 → (False ∧ p1))))) ∨ (p3 ∨ (p3 ∨ (p2 → (p3 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_711190541442417872508008981043 : ((((p3 ∧ ((p5 ∧ (p2 ∨ True)) ∨ p2)) ∧ (((p1 ∧ ((p2 ∧ p2) ∧ ((p5 ∧ (p1 → (p4 ∧ p2))) ∨ (p2 → p1)))) ∨ p4) ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234753540215659353270895934684 : ((p4 → (p2 → p4)) → ((p1 ∨ ((((p5 ∧ True) ∨ ((p5 → p4) ∨ ((p2 → (True → False)) ∧ p1))) ∨ (True ∨ p5)) ∧ True)) ∨ (p2 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309299820655127729044576048547 : (p2 ∨ ((((p4 ∧ ((((False → p3) → (p1 → (p1 ∧ False))) → p2) → (p2 ∨ (p5 ∨ False)))) ∨ ((p4 ∨ p1) ∨ True)) ∧ True) ∨ (p5 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_586687305406868163786563661869 : (((((True ∧ (((p1 ∨ p3) ∨ (False → (False ∧ p3))) ∧ ((((p2 ∧ (p3 → False)) ∧ ((True ∨ p4) ∨ p4)) ∧ p3) ∧ p4))) ∧ p2) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119353092886174243850875475697 : ((p3 → ((False → p4) → ((True ∧ (p5 ∧ ((p1 → False) ∧ ((False → (p5 ∨ p1)) ∨ (p4 → ((True ∧ True) ∨ p3)))))) ∧ p1))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51732471966809596957730165407 : ((((((p1 ∨ p1) ∧ p5) ∧ False) → ((p1 ∨ (True ∨ (p1 ∧ (p3 → False)))) ∨ p4)) ∧ ((((True ∧ p1) → p3) → (False ∨ p4)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148258020250520274407199724374 : (((p3 ∧ (((p3 → (p4 ∧ p4)) → p3) ∧ (p4 → ((p1 ∨ True) ∧ (p4 ∨ p2))))) ∨ (p2 ∧ (p5 ∧ True))) ∨ (((p2 ∨ True) ∨ p1) ∨ p4)) := by
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
theorem thm_5_vars_604875375906077640951337951816 : ((((p1 → ((((p3 ∧ p4) ∧ p1) ∨ ((False ∨ (p3 ∨ p5)) ∨ True)) ∨ ((False ∧ p4) → (((True → (p3 ∧ p5)) → p4) → False)))) ∧ True) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_634862021167483411456595765569 : ((((((p1 ∨ p1) ∨ ((p4 ∨ p4) ∧ ((True ∧ (((True ∨ (p3 → p5)) ∧ True) → (True → p4))) → False))) ∨ (p2 ∧ (p2 ∧ p1))) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42066098349518914191651832963 : ((((p5 ∨ p2) ∨ (((p3 ∨ (p4 ∨ True)) → (((p5 ∨ p3) → p3) ∧ (False ∧ (p2 → p1)))) → ((p2 → (p2 ∨ p4)) ∧ p5))) ∨ False) ∨ p1) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ (p4 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_877247444546167589774456945200 : ((((((True ∨ p4) ∧ ((False ∧ (False → (p2 ∨ p5))) → p3)) → (p3 ∧ ((p2 ∧ ((p1 ∧ p4) ∨ (p1 ∨ True))) ∧ p1))) ∧ (p5 ∧ p3)) → p1) ∧ True) := by
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
  have h6 : ((True ∨ p4) ∧ ((False ∧ (False → (p2 ∨ p5))) → p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h10 := h2 h6
  -- We need to get the right conjuct of h10 based on <expert-advice>.
  let h11 := h10.right
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49248669066993069307404664942 : (((True ∧ (((((((True → p5) ∨ (p4 → p4)) → False) → ((p5 → p4) → (p3 ∧ p2))) ∨ p1) → p4) ∨ True)) ∨ ((p2 ∨ p4) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38366170333638852983033239134 : (((((p3 ∧ ((p4 ∧ p4) ∨ (p2 ∨ p2))) ∨ ((p5 ∧ p4) ∨ ((p2 ∧ p4) → p5))) ∨ (((False → (False ∧ p2)) ∨ True) ∨ p1)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54285214341451883165461885149 : ((((p2 ∧ (p5 ∧ True)) → (p5 → (p1 ∨ p5))) ∧ (((p2 ∨ (p5 ∨ (((p2 → (False → (p4 ∧ p4))) ∧ p3) ∧ p3))) ∧ True) → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255527637557113628165223942950 : ((p5 ∧ p2) → (False ∨ ((p5 → (p3 → (((((False ∨ p5) ∨ False) ∧ True) ∧ ((True ∧ p1) ∧ True)) ∨ (((p2 → p3) ∨ p4) ∧ p1)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47310633712975995772224116747 : (((((p3 → p5) → p3) ∨ ((p2 ∨ (((p5 ∧ (False ∧ (True ∨ (p1 → ((p2 ∧ p2) ∧ p4))))) ∨ p5) → p4)) ∧ p2)) ∨ (True ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_89182426493193258444374102005 : ((((False → True) → p1) ∧ (((p3 ∨ p1) → (p4 → (p3 ∨ (p2 → (False → (p3 → (True ∧ p1))))))) → ((p5 → (True ∧ False)) → p5))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342306228810299200242860326743 : (p2 → ((p5 → (p1 ∨ ((p5 ∨ p1) ∧ ((p5 ∧ ((False ∧ p3) ∨ (p4 → p1))) ∨ (p1 → False))))) ∨ (True ∨ (False ∧ ((False ∧ p4) ∧ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41139818430487254108227411913 : ((((((p4 ∧ (p2 ∨ False)) → (False ∧ ((p5 ∨ False) ∧ ((True ∧ False) ∧ p1)))) ∧ ((p4 ∨ False) → True)) ∨ (p3 ∨ (False ∧ p1))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_660246436592635256643977654502 : ((((((p5 → p4) ∧ (p4 ∧ ((p1 → p2) → (p2 ∨ ((p3 → (p4 ∧ ((False → (p2 ∨ p1)) → False))) → True))))) ∨ p1) → (p1 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76318215982462368817719772230 : ((((True ∧ ((((p3 ∨ (((p3 → p5) ∨ True) ∧ (p2 → p5))) ∧ ((p3 ∧ p5) → p5)) → True) → (p5 ∨ p2))) ∨ (p1 → True)) → p1) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ ((((p3 ∨ (((p3 → p5) ∨ True) ∧ (p2 → p5))) ∧ ((p3 ∧ p5) → p5)) → True) → (p5 ∨ p2))) ∨ (p1 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340452538884636402086522204233 : (p2 → ((((p2 → True) ∧ (p4 ∨ (p3 ∧ (((True → ((p4 ∧ False) ∧ p5)) ∧ True) ∨ p3)))) ∨ ((((p2 → p4) ∧ p2) ∧ p2) → p4)) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- One of the premise coincides with the conclusion.
  exact h8
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678302303840266969932042009602 : ((((((p1 ∧ (((p4 → True) ∨ True) ∨ p5)) ∧ p5) → (((p3 → p5) → ((p1 → False) ∨ True)) → p2)) ∨ (p4 ∨ ((True → False) → p5))) ∨ False) ∧ True) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158309916026085996346272118174 : (((p4 ∧ (True ∨ True)) → (((((p4 ∨ p5) ∨ True) ∨ ((p3 ∨ p3) ∨ p3)) → False) ∧ (p1 → True))) ∨ ((p2 ∨ (p2 ∧ (p3 ∨ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136472206819619485016493247488 : ((((p5 ∨ p2) ∧ p5) ∧ (p1 → ((p3 ∨ ((False → (p3 → p1)) → ((p5 → ((p1 ∧ p3) ∧ True)) → p3))) ∧ False))) ∨ ((True ∧ p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115193772088101523248064670355 : ((((p2 ∨ (p5 ∨ p1)) ∨ ((False ∨ p2) ∧ (p3 ∧ False))) ∧ (p3 ∨ ((True ∨ p4) ∨ (p3 → ((p3 → (p1 ∧ False)) ∨ p2))))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199479797542364821427544689016 : (((p3 ∨ (((p3 → True) ∨ False) → p2)) ∨ p1) → ((p2 → False) ∨ (p5 → (((p2 → p5) → True) → (((p4 → (p3 → p1)) ∧ p2) → p2))))) := by
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
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- One of the premise coincides with the conclusion.
      exact h14
  case inr h15 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h16
    -- Implications on the right can always be decomposed.
    intro h17
    -- Implications on the right can always be decomposed.
    intro h18
    -- Conjunctions on the left can always be decomposed.
    let h19 := h18.left
    let h20 := h18.right
    -- One of the premise coincides with the conclusion.
    exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139238083545622589621975040663 : ((((p3 → p1) ∧ (p5 → (((p3 ∨ (False → ((True → p3) ∨ (True ∨ ((p3 ∨ p2) ∧ p3))))) → True) ∨ False))) ∨ False) → ((p5 ∧ p1) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68281935200269797733831485829 : ((p3 → ((p5 ∨ (((((p4 ∧ True) → (((p5 → p4) ∨ (False ∧ (False → p2))) ∨ p2)) → False) → p5) ∧ (p2 ∧ p3))) → (p3 ∧ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172319051220648061355930109827 : (((p3 → ((False ∨ p2) ∨ ((p5 → p5) ∧ True))) → ((True → p1) → (False ∨ p4))) ∨ (((((p5 ∨ p1) ∨ p4) ∨ p3) → False) → (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55476752130724755040543490416 : (((((True ∧ p1) ∨ p4) ∨ (p4 → False)) → ((p5 → ((False → (False ∨ p3)) ∨ (((p5 → False) ∧ p2) ∨ (p1 → p1)))) → (p3 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54357518738641444935282931859 : (((p3 ∨ (p2 ∧ (p1 ∧ (p5 → (False ∧ p1))))) ∧ ((((p4 → (True ∨ p3)) → (p1 → (True ∨ (True ∨ True)))) ∨ p1) → (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204125427065504486284873324286 : ((((False ∧ (p5 → p4)) ∧ False) ∧ p3) ∨ ((((p4 ∧ True) ∧ p1) ∨ p1) ∨ (p2 → ((False → p1) → (((p1 → (p1 → p1)) ∨ p2) ∨ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729720742712336074542863633522 : (((((p2 → p4) ∨ False) → (((((p2 ∨ ((p5 ∨ (p4 ∧ (True → p5))) ∨ (p4 ∨ p1))) ∨ (p4 → p2)) ∧ (True → p3)) ∨ p2) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114067943504572041838216660594 : ((((p1 ∨ (p4 ∨ (p1 ∧ ((p1 ∧ p4) → p1)))) → (p3 → ((p4 ∧ (p3 ∧ (p5 ∨ p5))) ∨ True))) ∨ (p5 → (p5 ∨ p4))) ∨ (p3 → p2)) := by
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
theorem thm_5_vars_191149197080501588020275696555 : ((((True ∧ p3) → p2) ∨ (p3 ∧ (p5 ∨ (p1 → True)))) ∨ ((p3 ∨ (p1 → (False → p5))) → (p3 ∨ ((p4 ∨ p5) ∨ (p4 → (p4 ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_648593868265928380275527838616 : ((((((True ∧ ((p4 ∧ (p5 → (p1 ∨ p2))) → p5)) ∨ ((((p4 ∨ p2) ∧ p4) ∧ True) ∨ (True → (p3 → p2)))) ∨ True) ∧ (True ∧ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44800430240001183769098107464 : (((((p3 ∧ p2) → p4) ∧ (True ∨ (False → (p4 → ((True → ((p1 ∧ ((p5 ∧ False) ∧ True)) → ((True ∨ p2) ∧ p2))) ∧ p4))))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_686634337149285952101745309351 : (((((p5 → p3) ∨ ((p3 ∨ (((True ∨ ((False → p2) → (p4 → p1))) ∧ p1) ∧ True)) ∨ p3)) → (((p1 ∨ p5) → p5) ∨ (True → True))) ∨ False) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Conjunctions on the left can always be decomposed.
        let h11 := h9.left
        let h12 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713626988964674398555477365711 : ((((((p5 ∨ (p5 → p4)) → p3) ∧ p2) → (p5 → (((p3 ∨ p1) → False) ∨ ((p3 ∨ (False → p5)) ∨ ((False ∧ True) ∨ (p5 ∧ p3)))))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1474451661601741495679451382 : (((p2 ∧ (p1 ∨ (p4 → ((p4 → (((((False ∨ p2) ∧ False) → p2) ∧ p2) ∨ (True ∨ True))) ∨ (True → True))))) ∨ p1) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46357686913976884724754655977 : ((((((False ∧ (((p1 ∧ p5) ∧ p4) → p3)) ∨ (p4 ∨ p3)) ∨ p5) ∧ ((p4 ∧ (p2 → False)) ∨ ((p5 ∧ p4) → p1))) ∧ (p2 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204285957491177077188645882356 : ((((p1 ∨ p3) → (p4 ∧ True)) ∧ p2) ∨ ((((p3 ∧ (p1 → p4)) → p3) ∧ (((p4 → p5) ∧ (True ∨ (p3 → True))) ∧ (p1 ∧ p4))) → p5)) := by
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
  cases h7
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h5.left
    let h10 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h11 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h12 := h6 h11
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h5.left
    let h15 := h5.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h16 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h15
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h17 := h6 h16
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134223273386497305714458885524 : (((((p2 ∨ (p5 ∧ True)) → (p5 ∧ p4)) ∨ (((p4 ∧ (p4 ∨ (p4 ∧ p1))) ∨ (p5 ∧ (False ∨ p1))) ∨ False)) ∨ p2) ∨ (True ∧ (True ∨ p1))) := by
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
theorem thm_5_vars_200033146953487574720821511999 : (((p2 ∧ ((True ∧ False) ∨ p2)) → (p3 → p3)) → (((p4 ∨ (p2 ∧ p4)) ∨ ((True → p3) ∨ (False → False))) ∧ (p2 → ((False ∧ True) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736351703276813412476813592677 : ((((False → p5) ∧ (((((p1 ∧ (p2 ∨ p2)) ∧ (p5 ∨ p5)) ∧ p2) ∨ ((p3 ∧ p3) ∧ p4)) ∨ ((True ∧ (p2 → (p4 ∨ True))) → True))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60470522407146778395184382374 : (((p5 → p4) → (((((p3 ∨ (True → (((p4 ∨ (p3 → True)) ∨ p4) ∨ p4))) ∧ p5) ∧ p3) ∨ (p1 ∨ (p2 → True))) ∨ (p4 ∨ p4))) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803824467032705229780089764994 : (((p3 → (((((((((p3 ∧ p2) ∨ False) ∧ False) → p2) → p5) → p3) → (p4 ∨ p4)) → ((p2 ∨ p4) ∧ (p4 ∧ p2))) ∨ (True ∨ p3))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_950136919523564120130644370635 : (((((p3 ∨ True) → False) ∧ ((((p2 ∨ p3) → ((p2 ∨ p4) → (p3 ∨ (p1 ∨ p4)))) ∨ ((((p2 ∧ p2) → True) → True) ∧ True)) ∨ p4)) → p4) ∧ True) := by
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
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h11 : (p3 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h12 := h2 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- One of the premise coincides with the conclusion.
    exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245549639208694844471533626908 : ((p3 ∧ True) ∨ (((((p2 ∧ (p2 ∧ p2)) ∨ p5) ∧ False) ∧ False) ∨ ((p2 ∨ True) ∨ (((p4 ∧ (p2 ∧ p4)) → (p4 ∨ (p4 → p2))) → p2)))) := by
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
theorem thm_5_vars_112003654817047339217648949152 : ((((False ∨ (False ∧ (p2 → p1))) ∨ ((((p3 ∨ p3) → ((p2 ∧ (p4 ∧ True)) → p5)) ∨ p2) ∨ (p5 → (p3 ∧ p2)))) ∨ False) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



