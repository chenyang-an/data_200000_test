variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323221510451527582365417355686 : (p5 ∨ (((((True ∨ False) ∧ (((p5 ∧ (False ∧ p4)) → p5) → p4)) ∨ p3) → (p3 ∨ (p1 ∨ ((p4 ∨ (p3 ∨ p3)) → p4)))) ∨ (p2 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h6 : ((p5 ∧ (False ∧ p4)) → p5) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h12 := h4 h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h17 =>
          -- One of the premise coincides with the conclusion.
          exact h12
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60228905638072433377148226557 : (((True → p3) → (((p2 ∨ ((p2 ∨ p3) → p5)) → (((p1 ∧ (((p3 ∧ p3) → p5) ∨ p5)) → p3) → (p4 ∨ True))) → (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587693426016592374690063967604 : (((((((False ∧ False) ∨ ((p3 ∨ ((p4 ∧ p1) ∨ (p5 ∧ False))) ∧ ((False ∧ True) ∨ (True ∨ ((True ∧ p1) → p4))))) → p5) ∨ p2) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48610520173744008095752344208 : (((((((p2 ∧ p4) ∧ ((p2 ∨ p5) ∧ p1)) ∨ (p3 ∧ ((p4 ∨ (p2 ∧ p4)) ∨ p5))) ∨ p2) → (p3 → p4)) ∧ ((False ∨ p4) ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147378269072274002799846698927 : (((((p1 ∨ p3) ∧ (((p1 → (p3 ∨ p5)) → p3) ∧ p3)) ∧ (p3 ∧ ((p4 ∧ p5) ∨ (p1 ∧ p3)))) ∨ True) ∨ (True ∨ (p4 ∨ (p2 ∨ p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158958874794192701331092351614 : ((p2 ∨ (p1 ∨ ((((False ∧ (((p3 ∨ p2) ∧ p5) ∧ True)) ∧ p1) ∨ (p3 → p5)) ∨ (p2 ∧ p2)))) ∨ (p2 → (p2 ∨ (False ∧ (p2 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59160872524530786538476335745 : (((False ∨ p2) ∨ (((p2 → p2) → (p1 ∨ ((p2 ∨ (p2 → (False → (p3 → False)))) ∧ (p5 → p4)))) ∧ ((p4 ∨ (p1 ∨ p5)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156647163420601041925871159788 : ((((((((False ∨ (p3 → (((p4 ∧ True) ∧ p2) ∧ p1))) ∨ p4) ∧ False) ∨ p4) → p2) → p1) ∧ False) ∨ (p4 ∨ (False ∨ ((p3 ∧ p1) → True)))) := by
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
theorem thm_5_vars_172107634345058608330591041909 : (((p1 → (p1 → ((True ∨ (p1 ∨ (True ∧ p5))) → (p5 ∧ False)))) → (p2 ∨ False)) ∨ (((p3 ∧ ((True → False) ∧ True)) ∧ False) → (p3 → p1))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h6.left
  let h8 := h6.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198236129866049375155467982933 : ((True ∧ ((p2 ∨ p5) ∨ ((p1 ∧ p5) ∧ p3))) ∨ ((((p4 ∨ ((p1 ∨ p5) → ((True ∨ False) ∨ (p4 ∧ (p1 ∨ p3))))) ∨ p2) ∨ p1) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233620530725760056131435349412 : ((p2 ∨ (p4 ∧ False)) → (p4 ∨ ((p4 ∨ p5) → (p3 → (((False → False) → (((p1 → ((p3 ∨ p1) ∨ p1)) → p5) ∧ p1)) → (p1 ∧ True)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h7 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h9 := h5 h7
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h12 : (False → False) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- False on the left can always be used.
        apply False.elim h13
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- One of the premise coincides with the conclusion.
      exact h15
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h16.left
    let h18 := h16.right
    -- False on the left can always be used.
    apply False.elim h18



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149954934627479179601940856462 : ((p4 ∨ (((p2 ∨ p4) ∧ ((p2 → p5) ∨ (((((p1 ∧ p2) → False) ∧ p3) → p2) ∨ (p5 → False)))) ∧ False)) ∨ ((p4 ∨ p2) → (p4 ∨ p2))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117365677242859725032199937034 : ((False ∧ (p4 ∨ (((p1 ∧ (((True → (p2 ∨ False)) ∧ p3) → ((False → p1) → p2))) ∨ (p5 → ((p5 ∨ p1) → True))) → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172837458732716374444112111338 : ((False ∧ ((p5 → (((True ∨ (p5 ∧ p3)) ∨ p2) ∨ (True ∨ (False → p1)))) ∧ False)) ∨ (((p1 ∧ (p1 ∨ (p5 → p5))) ∧ True) → (p5 ∨ p1))) := by
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
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172915500260221482913881126766 : ((p2 ∧ (True ∧ ((((True → True) → ((p4 ∧ p5) ∧ (p3 ∧ True))) ∨ p3) ∧ False))) ∨ ((((True ∧ p5) → (p3 ∧ p3)) ∨ (p3 ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137691035408899133247185480702 : ((p1 ∨ (((((p5 ∧ True) → p2) ∨ (p3 → (p3 → ((True ∨ (p3 → p2)) ∨ p5)))) → (False → (p5 → True))) → p2)) ∨ ((p5 ∧ p3) → p5)) := by
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
theorem thm_5_vars_214675019723312644483654264255 : (((p4 → p4) ∧ (p3 → p5)) ∨ (((((p5 → False) ∨ p4) → False) → (p1 → (p5 ∨ p2))) → (((True → ((p1 ∨ p5) ∨ p5)) → p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193083306861307456439526137373 : ((((True ∨ p2) ∨ (p1 → True)) ∧ ((p2 → p2) → p5)) → (((p1 → p3) ∨ (p5 → ((False → p3) → p5))) ∨ (p5 ∧ (p2 ∨ (p5 → True))))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699984170882837523122380084347 : ((((((p1 ∧ p2) → (p5 ∧ p4)) ∨ (True ∨ ((False ∨ p4) → p1))) → (((p1 → (p2 ∨ (p3 → p2))) ∨ (p2 ∨ (p3 → p4))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114828873786407389513364341842 : (((p4 ∨ (True ∧ (((p1 ∧ ((p4 → p1) ∨ False)) ∧ (True → p5)) → False))) ∧ (False ∧ ((p5 → False) ∨ (True ∧ (p3 ∧ p2))))) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168543426125808781035157581099 : ((p1 ∧ (((p5 ∧ p3) ∧ (p2 → ((p1 → (p2 → p5)) ∧ (p3 ∨ p4)))) ∧ (True → p1))) → (((p2 ∧ (p4 → False)) ∨ (p1 → p1)) ∧ p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h10
  -- One of the premise coincides with the conclusion.
  exact h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h1.left
  let h12 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h12.left
  let h14 := h12.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179536100893403614676899627459 : ((p1 → ((((True → p2) → ((p3 → p3) → False)) ∧ False) ∨ (p4 ∧ p1))) ∨ (((p1 → p3) ∨ (False → (False → (p4 ∧ p1)))) ∨ (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343296398543216325862476858025 : (p2 → ((True ∨ True) ∧ ((False ∨ (False ∧ (p4 ∧ ((p3 ∧ (p4 ∨ (p3 ∧ (((p5 ∨ p1) ∨ (p4 → p2)) ∨ p3)))) ∧ (False ∧ p4))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248742109602423373012969557693 : ((p3 ∨ p3) ∨ ((((p2 ∨ (p4 ∨ ((p5 ∨ False) ∨ False))) ∧ ((p1 ∧ True) ∨ ((p4 ∧ p3) ∧ (p4 → (False → (p1 ∧ p5)))))) ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156995830957000711488284360804 : ((((p2 ∨ (p2 ∧ (p4 ∨ p5))) ∧ (False ∧ ((((True → p5) ∨ p5) → (p4 ∧ p1)) ∨ p5))) ∨ True) ∨ (p2 → ((p5 ∧ (p5 → p4)) ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799043625972194077576505563194 : (((p1 → ((p1 ∨ p4) → (p2 ∨ (p1 → ((p1 ∧ ((p5 ∧ (((p4 → p1) → p3) → (p1 → p5))) ∨ (p5 → (p5 ∨ p4)))) ∨ p4))))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148008706943163031533862210736 : ((((((((p5 ∨ p4) → p3) ∧ p3) → ((p2 → p4) ∧ p5)) ∨ (p3 ∧ p3)) → (p2 ∨ False)) ∨ (True ∨ p4)) ∨ (p4 ∧ (p2 → (p4 ∨ False)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47023961186414955492490889820 : ((((p5 ∨ (p5 → (True ∨ (p3 ∧ (False ∨ ((p2 ∨ (p5 ∧ ((False ∧ (p1 ∨ (p3 ∧ p1))) → p3))) ∧ p4)))))) → False) ∨ (True → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_726073334664097968703817677330 : (((((False ∧ p5) ∨ p1) ∨ (((((p2 → p3) → (p3 ∧ p2)) → ((p3 ∨ p1) → (p4 ∨ (p4 ∨ (True ∨ p5))))) ∧ p5) → (p2 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227927497746930209675283340005 : ((p3 ∧ (True ∧ p4)) ∨ (p2 ∨ (((p3 ∨ ((p2 ∧ ((True ∨ ((p3 ∨ True) → (p4 ∧ p4))) ∧ p3)) → (p2 ∨ (False ∧ p3)))) → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ ((p2 ∧ ((True ∨ ((p3 ∨ True) → (p4 ∧ p4))) ∧ p3)) → (p2 ∨ (False ∧ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h2
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172966329048170156480074587220 : ((p4 ∧ (((p2 → (((p1 ∨ True) ∧ p2) ∧ p3)) ∧ False) ∧ ((p2 ∨ p1) ∨ p3))) ∨ ((p4 → p4) ∨ ((False ∨ (p3 ∨ p3)) → (p1 ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258669363526194870220188057745 : ((p5 ∨ p5) → (((p4 ∨ ((p5 → p5) → True)) → p2) → (p4 → (((p2 → (p5 → False)) ∧ p2) → ((((p4 ∨ p2) → p3) ∨ True) ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60118406028964156228117759488 : (((p3 ∨ p4) → ((p1 ∧ p4) → (((p2 → ((p5 ∨ (p1 ∨ False)) ∧ p1)) ∨ (p1 → p4)) → ((p2 → False) ∨ ((p1 ∨ p3) → p1))))) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h2.left
    let h6 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- One of the premise coincides with the conclusion.
        exact h5
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h5
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h2.left
    let h17 := h2.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h24
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701903405743399051705823766113 : ((((p1 ∨ (((p2 ∧ (True ∨ (p1 → p5))) → False) ∧ p4)) ∧ (p2 ∧ (False ∧ ((True ∨ (True → (p5 ∨ p5))) ∧ ((True ∨ p5) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316608122792126990423811290253 : (p3 ∨ (p4 ∨ ((((p3 → p1) ∧ ((True → ((p5 → False) → (p1 ∧ (p2 ∧ (True → ((p3 ∧ (p4 → p5)) ∧ True)))))) ∧ False)) ∨ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712262634373270194825685632635 : ((((((p1 → p4) ∨ (p2 → p4)) → p2) ∨ (((((p5 ∧ ((((p4 → p4) → p2) ∧ True) ∧ (p4 ∨ p2))) ∧ p3) ∧ p2) ∧ p3) → p2)) ∨ p1) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Conjunctions on the left can always be decomposed.
  let h12 := h10.left
  let h13 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h14 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313215737060705021919565898121 : (p3 ∨ (((p4 ∧ (p2 → p4)) ∨ ((((p5 → (((p2 ∨ (p1 → (False → p1))) → p2) → (p5 → (True ∧ False)))) → p2) → p4) ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739088369585886652470443783009 : ((((p3 ∧ p4) ∨ (p4 → ((p1 ∨ (((p2 ∨ p2) → (((p4 → p5) ∧ True) ∧ (p3 ∧ p4))) ∧ (((p4 ∧ p2) → p5) ∨ p2))) ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308744213864419243712522809473 : (p2 ∨ ((p4 → (((True ∨ p2) ∨ ((p4 → False) ∧ p4)) → (p2 ∧ (((p1 ∨ False) → (p3 ∨ (p2 ∧ (p4 → p3)))) ∧ (True ∨ False))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259370338117815922271391700863 : ((False → p3) → (((((p2 → p2) ∨ (p2 ∧ (p5 ∨ True))) → ((p4 ∧ p1) ∧ (((False → p2) → ((p4 → p3) ∧ False)) ∨ p2))) ∨ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175338708442325107129295340901 : ((p5 ∨ (((p5 ∧ True) ∨ ((False → p1) ∧ ((p1 → (p4 ∧ True)) → p4))) ∧ p4)) → ((((p2 ∧ (p2 ∨ (p1 ∧ p1))) ∨ p4) ∨ p2) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114635230585011596943546544366 : (((((((p1 ∨ p4) ∧ p5) ∧ (p3 → (((p5 ∧ p4) ∨ False) ∨ p4))) → p3) → p3) ∨ (False → (p2 ∧ ((p3 ∧ True) ∨ False)))) ∨ (p3 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_344799754755423949919592473194 : (p2 → (p4 → ((((False ∨ True) ∧ p3) → True) ∧ ((((True ∨ p5) ∧ p4) → ((((p5 → (False ∧ p1)) → (p4 ∧ p1)) → p5) ∧ p5)) ∨ p4)))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55239369011778448904156039248 : ((((p1 ∧ p2) ∧ ((p1 → p5) ∧ False)) ∨ ((p1 ∨ False) → ((True → p5) ∨ (p1 → ((True ∧ (p5 → ((True ∧ p4) ∧ p3))) ∨ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_585978533480678115929768729322 : (((((((((p3 → ((p5 → (((True → False) ∨ p2) ∨ p4)) ∧ p3)) → p5) ∨ (p2 ∧ p2)) ∧ p3) ∧ (p1 ∨ (p1 → p2))) ∧ False) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219819806768879758324373999058 : ((p3 → ((p5 ∨ p3) ∧ True)) → (((True ∧ p3) ∨ (p2 ∧ ((True ∨ (((p1 ∧ p1) ∧ (p1 ∧ ((False ∧ False) ∨ p2))) → False)) → p3))) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (True ∨ (((p1 ∧ p1) ∧ (p1 ∧ ((False ∧ False) ∨ p2))) → False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h10 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52382474281802562196057137218 : (((((p4 ∨ p1) ∨ (((p3 → p4) ∧ p2) ∨ p5)) → (p4 → (p2 ∨ False))) ∧ ((p2 ∧ False) ∧ (p4 → (p2 ∧ (False ∧ (True ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42612381113741957644630207970 : (((p3 ∨ (((p2 ∨ (((((p3 ∨ (p1 → p4)) ∨ (True → p4)) → p3) ∨ (p3 ∨ (p4 ∧ p5))) ∧ True)) ∨ (True → p3)) → p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173007425242358967231501805774 : ((p5 ∧ (p3 ∧ (((p5 → p2) → (p2 → p5)) ∧ ((p3 → (p3 → p4)) → p1)))) ∨ (p5 → ((p5 → ((p1 → False) ∨ (True ∨ True))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110712381909885841894775041315 : ((((((p4 ∨ (p3 → (True ∧ ((False → p2) ∨ (p4 → (True ∧ (False ∨ (p3 ∨ (p3 ∧ False))))))))) → p3) → False) ∧ p2) ∧ p3) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156848425368691593803288998764 : (((p4 → ((p3 → p1) → (((p3 ∨ (p5 → (False ∧ p4))) ∨ (p3 ∨ p1)) ∨ (True ∨ p2)))) ∧ True) ∨ (p5 → ((False ∨ p3) ∧ (p5 ∧ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40210080801474480258194261235 : (((((p5 ∨ False) ∨ (((False → False) ∧ (p3 ∨ ((p5 ∧ (((((p1 ∨ p3) ∧ p3) → True) ∨ False) ∨ p4)) ∧ True))) ∨ False)) ∧ True) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114568937619291492591192580525 : ((((p2 ∧ (p1 → ((p5 → (((False ∧ False) → p1) → True)) ∨ p2))) ∨ (p2 ∨ p2)) ∧ ((p5 ∧ ((p3 ∨ p4) → p2)) → p3)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803371347400136875051796210491 : (((p3 → ((p1 ∧ (p1 ∨ ((p1 ∧ (p1 ∧ ((p2 ∨ (p5 → ((p5 ∨ p5) ∧ False))) → ((p1 → p2) ∧ p4)))) ∨ (False ∨ p2)))) ∨ True)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656905330325839599026308902777 : ((((((p1 ∨ (p4 → p5)) → p5) ∨ ((p3 ∧ (((p2 ∧ (False ∧ p5)) ∧ False) ∨ ((False ∨ (True → p2)) ∧ p5))) ∨ True)) ∨ (p4 ∧ p5)) ∨ p5) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166339651837208494021530306668 : ((p5 ∧ (p3 → ((p1 ∨ (((((True → p5) ∨ p1) ∧ p3) ∧ False) ∨ p2)) ∧ (True ∧ p2)))) ∨ ((False → (p3 ∨ (True → p5))) ∧ (False → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227957449535012374624734734041 : ((p3 ∧ (p5 ∧ False)) ∨ ((((p1 ∨ (p4 ∨ (False ∧ p4))) ∨ (True ∧ p1)) → ((p5 → (p4 ∨ p2)) → (p1 ∧ (p4 ∧ (True ∧ True))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160022067720386542995630820407 : (((((p5 ∧ p2) ∨ p5) → (((p4 ∧ p3) ∨ ((p2 ∧ ((p2 → False) ∧ p2)) ∧ p4)) ∨ p5)) → False) → ((p3 ∨ ((p4 ∧ p2) ∧ p3)) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∧ p2) ∨ p5) → (((p4 ∧ p3) ∨ ((p2 ∧ ((p2 → False) ∧ p2)) ∧ p4)) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345499032917456957923285922628 : (p3 → ((((p2 ∨ ((p1 ∨ ((True → (p4 ∨ (p5 → p5))) → (p3 ∨ p4))) → p1)) ∨ True) ∨ ((True ∨ p2) ∧ ((p1 ∨ p3) ∨ False))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317328933239497356360279132267 : (p4 ∨ ((((p1 ∨ ((p2 ∨ False) → (p1 ∧ (p1 ∨ (p4 ∨ False))))) ∨ (((p1 ∧ p2) ∨ p4) ∧ p2)) → (p3 ∨ ((p4 ∧ p3) → p4))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- One of the premise coincides with the conclusion.
      exact h9
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
      -- Implications on the right can always be decomposed.
      intro h17
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- One of the premise coincides with the conclusion.
      exact h18
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Conjunctions on the left can always be decomposed.
      let h22 := h21.left
      let h23 := h21.right
      -- One of the premise coincides with the conclusion.
      exact h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199710834408446805890907984444 : (((p3 ∧ ((p1 ∨ p4) ∧ (p1 ∨ p4))) → p2) → (p4 → (((p1 ∧ False) ∧ ((True → (p5 → p3)) → ((p5 ∧ p1) ∨ (p1 ∧ p3)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193892237654376018378437922957 : ((False ∨ (p3 ∧ ((p4 → p1) ∨ ((p1 ∨ p5) → True)))) → ((((p5 → (((p1 → True) → p1) ∨ p5)) ∨ p1) ∧ ((p2 ∨ p4) → True)) ∨ p4)) := by
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
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225367102489873749243246436738 : (((p2 ∨ True) ∧ p2) ∨ (((p2 → ((True ∨ p2) → (p3 → p3))) ∧ p1) ∨ (p2 ∨ (p3 → (((True → False) ∧ True) → ((p3 ∨ p3) ∧ p2)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h7
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265760915064360094227466849613 : (True ∧ (p4 ∨ (((p3 → (p2 → ((p5 ∨ p4) → (((((p4 ∨ False) ∧ p3) ∧ p5) ∧ (p5 ∧ (p2 ∨ (p5 ∧ p4)))) ∨ p2)))) → p3) → p3))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 → (p2 → ((p5 ∨ p4) → (((((p4 ∨ False) ∧ p3) ∧ p5) ∧ (p5 ∧ (p2 ∨ (p5 ∧ p4)))) ∨ p2)))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44889741579329219127950139234 : (((((p2 ∨ p3) → p1) → (((p1 → (True → ((p1 ∨ (((p3 ∨ p4) ∧ p2) ∧ p5)) ∧ p4))) → (False ∧ (p5 ∧ p5))) ∧ True)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51097762509344253202882503395 : ((((((p4 → True) ∨ (p5 → p2)) ∧ (False ∧ (((p2 ∨ p5) ∨ p4) ∨ (p4 ∨ p2)))) ∧ True) ∨ ((False ∨ (p4 ∨ (p1 → p1))) ∨ p2)) ∨ False) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157766992203816454461648823007 : (((p5 ∨ ((p5 ∧ (p3 ∧ False)) ∧ (p5 ∧ (p1 → (p2 → p5))))) ∧ (((False ∧ True) → p3) ∨ True)) ∨ (p4 → ((True ∨ (p2 → p2)) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54918131992682508152855137599 : ((((((p5 → p4) → p2) → p2) → p5) ∧ ((p1 → (((True ∧ (True ∨ p3)) ∧ p5) ∧ ((((p5 → p2) → p5) ∧ True) ∨ p1))) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_779497800219265331822699677043 : (((p2 ∨ ((((((p1 → p1) ∧ (p1 ∨ p2)) → p2) ∨ True) ∧ (p2 ∨ (p4 ∧ ((p1 ∨ (True → (True → False))) ∧ (p4 → p3))))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315261958022880635481452847294 : (p3 ∨ ((False ∨ ((p1 ∧ False) ∧ p2)) ∨ (p4 ∨ ((((((True → p4) ∨ (p5 ∨ (p2 → p1))) ∨ False) ∧ (p2 ∨ p3)) ∨ p3) ∨ (p2 → p2))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197705090768826785485953710137 : (((p3 → ((p4 → p1) ∧ p2)) → (p1 → False)) ∨ (((p4 ∨ ((p5 → p2) ∨ p4)) → (p2 → (p3 ∨ p2))) ∨ (p5 ∧ (p2 → (False ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60117912228911236151657089773 : (((p3 ∨ p4) → ((p2 → (True ∧ p4)) ∧ (((p4 → p3) → ((p5 ∨ p3) → (((p2 ∧ p4) ∧ p5) → (p1 ∨ p1)))) → (p1 ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40843973883031061623904928905 : ((((p4 → (False ∨ (((False ∨ (((p1 → False) ∧ (p1 ∧ ((p3 ∧ p3) ∧ (False ∧ False)))) → p4)) ∧ True) ∨ (False ∨ p5)))) → p4) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_82364277906233851424260075924 : ((((p1 ∨ ((True ∨ ((p3 ∧ p1) ∨ p5)) → False)) ∧ ((True ∨ ((p1 ∨ (p5 → p3)) ∧ p2)) → True)) ∧ (((p4 ∨ p5) ∧ p3) ∧ p2)) → p1) := by
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
    let h7 := h3.left
    let h8 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h9 := h7.left
    let h10 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h11 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h3.left
    let h15 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h14.left
    let h17 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h19 : (True ∨ ((p3 ∧ p1) ∨ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h20 := h13 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
      have h22 : (True ∨ ((p3 ∧ p1) ∨ p5)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h13, we can now drive its conclusion.
      let h23 := h13 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739164601184325082616769396330 : ((((p4 ∧ True) ∨ (True → ((((p1 ∧ p2) ∧ (((p2 → p5) → p3) → (p2 ∧ False))) ∧ (p1 ∧ p1)) ∨ (p3 → (p3 → (p1 → p3)))))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175334098827289366986046244552 : ((p4 ∨ (True → (True ∧ ((p3 ∨ p4) ∧ (((p1 ∧ (p3 ∧ p4)) ∨ p4) ∨ p4))))) → ((p4 ∨ (p3 ∧ ((p1 → True) ∧ (p4 ∧ p3)))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606887920826287270300423250762 : ((((((p2 ∧ ((p5 → ((((p3 → p2) ∧ (True ∨ p5)) ∧ True) → (p1 → (False → False)))) ∧ True)) → (p2 → (p1 ∧ p2))) ∧ p1) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151940154661570707245443262908 : (((p1 ∧ (p5 ∧ ((p4 ∧ ((p2 ∧ p2) ∧ p1)) → (False → False)))) ∧ ((p5 → ((True ∧ p4) → p5)) ∨ False)) → ((p5 → (p4 ∨ False)) ∨ p1)) := by
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
  cases h3
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_552207148144977218589724789 : ((((p4 → p3) ∧ ((((((p1 ∨ p3) → ((False ∨ p1) → p2)) → p3) → (p4 ∨ p2)) ∨ ((p4 → p2) ∧ p2)) ∧ p2)) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233814538350531692255687733428 : ((p3 ∨ (p3 → p4)) → ((p1 ∨ ((((((p3 ∨ p3) ∧ p1) → p2) ∨ (p1 → False)) ∧ (False → (p1 → p5))) → p1)) → (p2 → (p1 ∧ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h8 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : (((((p3 ∨ p3) ∧ p1) → p2) ∨ (p1 → False)) ∧ (False → (p1 → p5))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h13 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h14 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        -- Implications on the right can always be decomposed.
        intro h15
        -- Implications on the right can always be decomposed.
        intro h16
        -- False on the left can always be used.
        apply False.elim h15
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h17 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h18 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h19 : (((((p3 ∨ p3) ∧ p1) → p2) ∨ (p1 → False)) ∧ (False → (p1 → p5))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h20.left
        let h22 := h20.right
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h23 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h24 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        -- Implications on the right can always be decomposed.
        intro h25
        -- Implications on the right can always be decomposed.
        intro h26
        -- False on the left can always be used.
        apply False.elim h25
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h27 := h7 h19
      -- One of the premise coincides with the conclusion.
      exact h27
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h29 =>
      -- One of the premise coincides with the conclusion.
      exact h28
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h28
  case inr h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h32 =>
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h33 : (((((p3 ∨ p3) ∧ p1) → p2) ∨ (p1 → False)) ∧ (False → (p1 → p5))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h34
        -- Conjunctions on the left can always be decomposed.
        let h35 := h34.left
        let h36 := h34.right
        -- Disjunctions on the left can always be decomposed.
        cases h35
        case inl h37 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h38 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        -- Implications on the right can always be decomposed.
        intro h39
        -- Implications on the right can always be decomposed.
        intro h40
        -- False on the left can always be used.
        apply False.elim h39
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h41 := h31 h33
      -- One of the premise coincides with the conclusion.
      exact h41
    case inr h42 =>
      -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
      have h43 : (((((p3 ∨ p3) ∧ p1) → p2) ∨ (p1 → False)) ∧ (False → (p1 → p5))) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h44
        -- Conjunctions on the left can always be decomposed.
        let h45 := h44.left
        let h46 := h44.right
        -- Disjunctions on the left can always be decomposed.
        cases h45
        case inl h47 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h48 =>
          -- One of the premise coincides with the conclusion.
          exact h3
        -- Implications on the right can always be decomposed.
        intro h49
        -- Implications on the right can always be decomposed.
        intro h50
        -- False on the left can always be used.
        apply False.elim h49
      -- We have shown the premise of h31, we can now drive its conclusion.
      let h51 := h31 h43
      -- One of the premise coincides with the conclusion.
      exact h51



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149077771422335401762359661459 : ((((p5 ∧ p1) → p1) → (p2 ∨ (False ∨ (((True → p1) ∧ p3) ∨ (p5 → ((p4 → p5) ∧ (p1 → p5))))))) ∨ (p3 ∧ ((p3 → p2) ∨ p5))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_430720353860723562813105802811 : (((((p3 ∨ (p1 ∧ p4)) → ((((((p3 ∨ True) → False) → p2) ∨ p2) → (((p1 ∧ (True ∧ p2)) → True) ∧ p5)) ∨ True)) ∨ (True ∨ p5)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_654960412873232002188687069720 : ((((((p4 → ((p4 → p2) ∧ p4)) → (p4 ∨ ((p5 ∧ ((True → p3) ∨ ((p3 ∨ p2) ∨ (p5 → p2)))) → p4))) → False) ∨ (p4 → p4)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_225452976229270090143498509813 : (((p4 ∨ False) ∧ p4) ∨ (((False ∧ (True ∧ p2)) ∧ (p3 ∨ (((p2 ∨ (p4 → (p3 → p2))) ∨ True) → p5))) ∨ ((p2 ∧ p4) → (p4 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48534113386899556913611207065 : ((((p2 ∨ (p2 ∧ (((((p2 ∧ p3) ∧ p3) ∧ p3) → (p1 → ((False ∨ (p1 ∧ p2)) ∧ p4))) ∧ p1))) ∨ p5) ∧ ((p4 → p2) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340733320142755025263934229259 : (p2 → ((((((p3 ∧ (((p3 ∧ p4) → p5) ∨ (p5 → p2))) ∨ p4) ∧ ((p3 → False) → (p4 ∧ ((p2 ∨ True) → p5)))) ∨ p3) ∨ p2) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51304027755833473163403538470 : (((p1 ∨ (((p2 ∧ p1) ∧ (p5 ∨ ((p5 ∨ p5) ∨ (p3 ∧ (p2 → p4))))) ∨ (True ∨ p3))) ∨ (p3 ∧ (((p5 → p3) ∨ True) ∧ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_55329536115375307816649268157 : (((p4 ∨ (((p3 ∨ p5) → p5) ∨ p1)) ∨ ((p2 ∨ ((((p5 ∨ p3) → (True ∨ p2)) → p5) ∨ (p5 ∧ False))) ∨ (p4 → (True ∨ False)))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_117359352048071347509673048100 : ((False ∧ (False ∨ ((((p1 ∨ p5) ∨ (p4 ∨ (p3 ∧ (((((p5 → p1) ∨ p1) → (True ∨ p1)) ∨ p4) → p2)))) → p1) → False))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264550079747361277682827472989 : (True ∧ (((p3 ∨ p4) ∨ p5) ∨ (((p1 ∧ (p1 → p4)) → (p3 ∧ p5)) → (((False ∨ p5) ∨ ((p5 ∧ (p3 ∧ False)) → False)) ∨ (p4 ∨ p5))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345627978461455347407091968353 : (p3 → ((False ∧ ((p5 → False) ∧ (((((p3 ∨ False) ∧ False) ∨ p1) ∧ ((p1 ∨ False) ∧ (((False → True) ∧ p2) ∨ p3))) ∧ (p3 ∧ p4)))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207625042023249014868381760857 : ((((p4 ∨ (True → p5)) → True) → p1) → ((p2 → (p3 → (p5 ∧ (p1 ∨ p4)))) → ((p3 → (p4 ∧ ((p4 → True) ∧ False))) ∨ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p4 ∨ (True → p5)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_341761485805414702327194121916 : (p2 → ((p4 ∨ ((p5 → (((p4 ∧ (p4 ∧ (p3 ∨ False))) ∧ (False → p4)) ∨ p1)) ∨ ((p1 → ((p3 → True) ∨ p1)) ∧ p2))) ∨ (False ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167623247082419837431786318310 : ((((p5 ∨ (p1 → (((False ∨ p4) ∧ False) → (p5 ∧ (False ∧ p3))))) ∨ True) → (p1 ∧ False)) → (((((p2 → True) ∨ p2) → p2) → p1) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p5 ∨ (p1 → (((False ∨ p4) ∧ False) → (p5 ∧ (False ∧ p3))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((p5 ∨ (p1 → (((False ∨ p4) ∧ False) → (p5 ∧ (False ∧ p3))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187216342253599998686601473947 : (((False → p3) → (False ∧ ((p5 ∨ p5) ∧ ((p2 ∧ p3) ∨ p4)))) → ((p1 ∨ p4) ∨ ((p1 ∧ (True ∧ p5)) ∧ ((p4 ∨ False) ∨ (False → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66326071036458685184922461454 : ((p5 ∨ (p1 ∧ (((True ∧ p3) → (((p3 ∨ p5) ∨ ((p5 → ((p1 → p2) ∧ (p4 → (True ∨ (False → p2))))) ∧ p2)) ∨ p5)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48416353791531905780895594041 : (((p2 → ((p2 ∨ False) ∨ (p5 ∧ (p3 ∧ ((p5 ∧ ((p5 → p4) → ((p4 → (p3 → (p4 ∧ p2))) → p5))) → p3))))) → (p5 ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713515203662295240250016348208 : ((((p5 → (((p2 ∨ False) → p4) ∧ p4)) ∨ (p3 ∨ (p2 → (((p1 → p1) ∧ ((p1 ∨ p1) ∨ ((p4 → (p4 → True)) → p5))) ∨ True)))) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190482719382375122491163663757 : ((((True → (p2 → (p4 → (p5 ∧ p5)))) ∧ True) → p1) ∨ (((p3 → (((p4 → (p1 → p4)) → p4) ∨ (p4 ∧ (False ∨ p4)))) → False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184082774748414510379663172993 : ((((p4 → (False ∨ (p5 → p3))) → ((p5 → p2) → p2)) ∨ True) ∨ (p5 ∧ (True ∧ (p2 → (False ∨ (((p4 → (p2 ∨ False)) ∧ p2) ∨ p1)))))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



