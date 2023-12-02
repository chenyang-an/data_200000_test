variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166917214212577674771493085486 : ((((((p1 ∨ p2) ∧ p2) ∨ p5) ∨ (True ∧ ((p5 → (p5 ∨ False)) → (False ∨ True)))) ∧ p2) → ((p4 → p3) → (((True ∨ True) → p5) ∨ p2))) := by
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
    cases h5
    case inl h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68763917011770400655464786535 : ((p4 → (((((p1 ∧ p1) ∨ ((p5 ∨ p1) → (p4 ∧ False))) ∧ p4) ∨ False) ∨ (((p5 ∧ False) → p1) ∨ (((p3 ∧ False) ∨ p1) ∧ p2)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612193029845256646661703251017 : (((((((p4 ∧ (False ∧ p5)) ∧ (p5 ∧ False)) ∨ (((p5 → (p3 ∨ p3)) ∨ False) ∨ (p2 → (False ∨ (True ∧ p4))))) ∧ (p3 ∧ True)) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603396699911257152954891890388 : ((((p3 ∨ (((p3 ∨ (((False → (p2 → (p4 ∨ p4))) → ((p5 ∨ p2) → p5)) → False)) ∨ (((p4 ∧ p5) → p1) ∨ p1)) ∨ True)) ∧ True) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166198044790195413075671380377 : ((p1 ∧ (((p1 ∧ True) ∧ p3) → (((((p2 ∧ p5) ∧ p4) ∧ p5) ∨ p2) ∨ (p3 → p1)))) ∨ (((p5 → p5) ∨ p3) ∨ (p2 ∧ (p1 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112783144008427228546517310276 : (((((p3 → p3) → ((False → (p2 ∨ True)) ∨ p2)) ∨ ((p5 → p1) → ((((True ∧ (False ∨ p5)) ∨ p4) ∨ False) → p3))) → p2) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115677888191744952934167628771 : (((p2 ∧ ((p2 ∧ p5) ∨ (p1 ∧ False))) ∨ ((((True → (p5 ∧ ((False → p1) ∧ p2))) ∧ p4) ∧ (p1 → (p4 ∨ p4))) ∧ p4)) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350110857817151091179106535808 : (p4 → ((((p1 ∧ (p3 ∨ (p5 ∧ ((False ∨ (p4 ∨ p5)) ∧ False)))) ∧ (True ∨ (p5 ∨ (True → p5)))) ∨ (((p2 → p3) ∨ True) ∨ False)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254488762889505007062124395334 : ((p3 ∧ True) → (True ∧ ((((True ∨ p2) → (((p5 ∧ p1) ∨ (p3 ∨ ((p1 → False) → p5))) ∧ p4)) ∧ (p2 ∧ (p5 ∨ (True → p2)))) ∨ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197708442101633922398680883254 : (((p5 → ((p3 ∧ p3) ∧ p1)) → (False ∧ True)) ∨ (((p4 ∧ (p1 ∨ p1)) ∧ (p4 ∧ ((p1 ∨ p2) → (False ∧ p1)))) ∨ (p2 → (True ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260127365797491786092089693801 : ((p2 → p1) → (((p2 ∨ (True → p2)) ∨ True) ∧ (p4 ∨ (p2 ∨ (True ∨ ((((False → (((p1 ∧ p2) ∧ p3) ∨ p3)) → p2) ∧ p4) ∧ p5)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186246600432940469591444142920 : ((((((p2 ∧ p4) ∨ p4) ∨ (p2 ∧ (p4 ∨ p3))) ∧ True) → p2) → (((True → p5) ∨ (p5 ∨ (True ∨ p5))) ∨ (p1 → (p3 → (p2 ∨ p2))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167185894541242939944128407311 : (((True ∧ (p2 → (((p4 → (p4 → (((p2 → False) → p3) ∨ p3))) → p5) → p4))) ∨ p3) → ((p1 ∨ ((p3 → p5) ∨ (True ∨ p3))) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
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
theorem thm_5_vars_264071681027966880766740827268 : (True ∧ ((((p4 → p1) ∨ (p1 ∨ p1)) → (False ∨ (p3 → p1))) ∨ (True ∧ (True ∨ (False ∨ (p3 ∧ (True → (((p1 ∧ True) → p4) ∨ False)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_171524117407194625439983661996 : (((((((True ∨ p1) ∧ ((p4 ∧ p2) ∨ p2)) ∨ (p4 ∧ p3)) ∧ p3) ∨ True) ∨ p4) ∨ ((((p5 ∧ p1) ∨ ((p1 ∨ p3) ∧ p1)) ∧ p3) → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301566066797896701256861582429 : (False ∨ ((p2 ∨ (True ∧ p2)) ∨ (True ∧ (((False ∧ (p3 ∧ (p2 → p3))) ∨ True) ∨ ((p2 ∧ p2) ∨ ((((False ∧ p5) ∨ p5) ∨ p1) ∨ True)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_383074568736503655619703832359 : (((((p5 ∧ ((p2 → p3) ∧ ((((True ∨ p2) → False) → (p1 ∨ (((((p5 → True) ∧ True) ∨ p4) → False) ∨ False))) → p4))) ∨ p4) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244431345329793863247119213423 : ((False ∧ p2) ∨ (((((p4 ∨ (p2 ∨ p4)) → ((False → p5) ∨ False)) → ((p3 ∨ (False → ((p5 ∨ p3) ∧ (True ∨ True)))) ∧ p3)) → p3) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∨ (p2 ∨ p4)) → ((False → p5) ∨ False)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h2
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702896681240348389864132987406 : (((((p1 ∨ ((p4 ∧ p2) ∨ p2)) → ((p4 ∧ True) → False)) ∨ (((p1 ∧ p2) ∧ p3) ∧ ((p4 → p3) ∧ (p3 → ((p4 → p5) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118714970181887891256637166326 : ((p5 ∨ ((((((p4 → p1) ∨ (p3 ∧ (False ∧ (p5 → (p3 ∨ p2))))) ∧ (True → (True ∨ p5))) → p4) ∨ p3) ∨ (True ∧ p5))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223371582038139421670340638256 : ((True ∨ (p1 ∨ p3)) ∧ (((p2 → (p3 ∨ (True ∧ ((p2 → ((True ∧ (p5 ∨ (p5 ∨ False))) ∧ p2)) ∨ False)))) ∧ p5) ∨ ((p1 ∧ True) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303943763591798427803791080806 : (p1 ∨ ((((p5 → (p1 → (False → p1))) → False) → (p5 → (p2 ∨ ((((True → p4) ∨ p3) → (False ∧ (False ∨ (p1 ∨ False)))) ∨ p5)))) ∨ p5)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49404322570042553983010076480 : ((((((p1 ∧ p2) ∨ p5) ∧ (((p5 ∨ p3) ∧ p2) ∨ ((p1 ∨ ((p2 → p5) ∧ (p2 ∨ False))) → p3))) ∧ p4) → ((p1 ∨ p1) ∨ p5)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739379023735832992563442378225 : ((((p4 ∧ p5) ∨ (((((((p4 ∧ p3) ∧ (False ∨ p2)) ∧ p2) ∨ True) → (p5 ∧ ((False ∧ p1) ∧ p2))) ∧ True) ∧ ((p4 ∨ p5) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197225358073637077769782978697 : ((((p4 ∨ ((p1 ∧ True) → p2)) ∨ p3) → p4) ∨ ((p5 ∨ (True → p2)) ∨ (((((False → p3) ∨ False) → p4) ∧ p5) → (p4 ∨ (True ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40675295912632579566446301604 : (((((p3 ∨ (((False → True) ∧ (p2 → ((p4 → p2) ∨ (False ∨ (p1 ∨ p2))))) → (p2 ∨ p3))) ∧ (p1 ∧ (p3 → p4))) → False) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56608026674582889409878284765 : (((p5 → ((p5 ∨ p3) → True)) → (p3 ∧ (True → ((((False → (p5 ∨ p1)) ∧ ((False → p5) ∨ p5)) ∧ (p5 ∧ p3)) ∧ (p3 ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46043473624803180620363608801 : ((((True → ((((False ∨ (p1 → (p1 ∧ True))) ∧ (True ∨ p5)) → (p2 ∨ (p1 ∧ True))) ∨ (p2 ∨ (True ∧ p2)))) ∧ p5) ∧ (False → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249857269720090019069978845719 : ((True → False) ∨ (((((False → (p4 → p1)) ∧ p2) → p5) ∨ (True → ((p3 ∧ p4) ∨ True))) ∧ ((p3 ∨ (True → ((True ∨ p5) ∨ p3))) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313951817308354629741559119616 : (p3 ∨ (((((p4 ∧ p2) ∨ (p3 ∨ ((p5 ∧ ((False ∧ False) → (p5 ∨ p4))) → ((p1 ∨ p5) → p3)))) ∧ p4) ∧ (p3 ∨ p5)) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98827907024263470339123453569 : ((True → ((p4 ∨ (p1 ∨ (((((((p1 ∧ ((((False ∨ True) ∧ p2) ∧ False) ∨ p2)) → p3) ∨ p4) ∨ True) ∨ p4) ∧ p4) ∧ p5))) ∧ False)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694367810561753907723965407013 : (((((True ∨ True) ∧ (p4 ∧ (p3 ∨ (((False ∧ (p5 ∧ p5)) ∨ p3) ∨ True)))) ∨ ((p5 ∨ (p2 ∧ p5)) → (p4 ∨ (p1 ∨ (False ∨ True))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612652210746391519095891827160 : ((((((False ∧ (((p1 ∧ (p4 ∧ True)) ∨ False) ∧ (p3 ∨ ((p1 ∧ True) ∧ (True ∧ True))))) ∨ ((p1 → p1) ∨ p1)) ∨ (p2 → False)) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_687504120863949309245411931593 : (((((p1 ∨ ((p1 → p4) → ((((p2 ∧ True) ∨ (p4 ∧ p4)) → p1) ∧ False))) ∨ p5) ∧ (True → (True ∧ ((p1 ∧ (p4 → True)) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_71529802371901266923541877415 : ((((p5 ∨ p4) → ((False ∨ (((p1 ∧ True) ∨ (((p2 ∧ p4) ∨ ((p1 ∧ p2) ∧ (p4 ∨ False))) → p3)) ∨ p4)) ∧ (True → p3))) ∧ p5) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h8 := h6 h7
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192813440125183199799701538913 : (((p1 → ((p5 ∨ p4) ∧ (p5 → (p2 ∧ True)))) → p4) → (p2 → (((p2 ∧ p4) ∨ False) ∨ (p2 ∧ (False → (False ∧ (p5 ∨ (p4 ∧ p3)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149032784014630619274189348029 : (((p1 ∧ (p2 ∧ p5)) ∨ ((False ∧ (p1 ∨ p2)) ∨ (False → ((p1 ∧ (p1 → True)) ∨ (p3 ∨ (p4 ∨ p4)))))) ∨ (p3 ∧ (True → (p3 ∧ True)))) := by
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
theorem thm_5_vars_781576285665087717581475567575 : (((p2 ∨ (False ∨ (p4 ∧ (((p2 → False) ∨ p5) ∨ ((((p3 ∨ ((p5 → (p2 ∨ p4)) → p4)) → p1) ∨ p2) ∨ ((False ∧ p1) ∧ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41428352294746916169392620205 : (((((p1 ∨ ((True ∧ True) ∧ ((((p3 ∧ p4) ∧ p3) → p4) ∧ p1))) ∨ p3) → (((p2 ∧ ((p4 → False) ∨ p4)) → p1) ∧ p3)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65038621842732445301496142407 : ((p2 ∨ (True ∧ (((((p1 → True) → (True → (p1 ∧ (((((p3 → (p5 ∧ p5)) → p3) ∨ p5) ∧ p1) → p1)))) ∨ p4) ∧ p3) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661132835987826442474368285746 : ((((((True ∨ (p2 → (p4 → ((p2 ∧ (((False ∨ (False ∧ True)) ∧ (p4 ∨ p5)) ∧ False)) ∧ p1)))) ∧ True) ∨ (p2 ∧ p2)) → (p1 → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234779060089741364427986098931 : ((p5 → (False ∧ p1)) → (((((((p4 ∧ (p2 → False)) ∨ p3) ∧ (True → p3)) → (p5 → p2)) ∨ (p3 ∨ (p5 → (p4 ∨ False)))) ∧ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_856576383000649094459552126187 : ((((((p5 ∨ (p5 ∨ p4)) ∧ ((((((p2 ∧ False) → False) ∧ (p5 ∨ p1)) → p4) ∧ p4) ∧ ((True ∧ (p1 ∨ True)) ∨ p2))) ∨ True) → p3) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p5 ∨ (p5 ∨ p4)) ∧ ((((((p2 ∧ False) → False) ∧ (p5 ∨ p1)) → p4) ∧ p4) ∧ ((True ∧ (p1 ∨ True)) ∨ p2))) ∨ True) := by
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
theorem thm_5_vars_137767139291012070932944512346 : ((p2 ∨ ((p1 → ((False ∨ ((p2 ∧ ((p4 ∨ p4) → p2)) ∨ (p4 ∧ (p3 ∨ False)))) → p5)) ∧ (p2 ∨ (p1 ∧ p5)))) ∨ ((p2 → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159809204415888132521636511381 : (((p5 ∧ ((p5 → ((((p3 ∨ True) ∨ (p4 → (True ∨ p3))) ∨ False) ∨ True)) → (p4 → p4))) ∨ p1) → (((p4 ∧ p3) ∨ (p3 → p1)) ∨ p5)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38977955193788372081092845800 : ((((p2 ∧ p5) ∧ (((p5 → (p1 ∨ ((((p3 ∧ p4) ∨ p1) → False) → p4))) ∨ (((p3 ∨ p1) ∧ p5) ∧ p1)) ∧ (p2 → False))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134711404155703420211154456080 : (((((p2 ∧ False) → p1) ∧ (p4 → ((True ∧ False) ∧ ((p4 → True) ∧ ((False ∨ p3) ∧ (p2 ∨ (p3 ∨ p5))))))) → p5) ∨ (True ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319662318892579371892441256264 : (p4 ∨ (((((False ∨ p5) ∧ (False → False)) ∧ p2) ∨ p5) → ((p1 ∨ (p2 ∧ (p2 → (p5 → (p1 ∧ p3))))) ∨ ((False ∧ (p4 ∨ p3)) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337673829683933582041773794089 : (p1 → ((p1 ∧ ((p1 ∨ False) → (((False → (True ∧ True)) → (p2 ∨ (False ∨ p3))) ∨ (p3 → p3)))) ∨ (((p5 ∧ False) ∨ (True → False)) ∧ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158462126478514383386064975222 : (((p1 → p3) ∨ ((p1 ∨ ((True → (((p5 ∧ (p1 ∨ p2)) ∨ (False ∨ p2)) ∨ p2)) ∧ p3)) ∨ True)) ∨ (p5 ∧ ((False ∨ p1) → (True → p2)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135965236242467231941248934901 : (((p4 ∨ ((((p3 ∧ p4) → (p4 ∨ p4)) → False) → p4)) ∧ ((True → p4) ∨ ((p5 ∧ (True ∧ (True ∨ True))) ∨ False))) ∨ ((True ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804397543704317174945537977626 : (((p3 → (((p4 ∧ ((p1 ∨ (p4 → False)) ∨ (p1 ∨ p5))) ∧ p3) ∨ (((p2 → ((((p2 → False) → p2) → p1) → p3)) → True) → p3))) ∨ p3) ∧ True) := by
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
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113205425813583784935177039508 : (((((True → (True ∨ (p3 → (p3 → ((False ∧ (p1 ∨ p1)) ∨ ((False ∨ p1) ∧ p5)))))) → (p5 ∧ p2)) ∨ p4) ∧ (p5 ∧ p1)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351816378844525073476714027266 : (p4 → (((((((p1 ∧ p1) ∧ p1) ∧ p2) ∧ p1) ∧ p1) ∨ (p1 → p1)) ∨ (p5 → ((p1 → True) → (True → (p1 ∨ ((True ∧ p3) ∧ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_643546285673626557878934061938 : ((((p4 ∧ ((True ∨ True) ∧ ((False → (((p1 → p3) → p3) ∨ p5)) → (False ∨ (True ∨ ((p3 ∨ (p2 → (p1 ∧ p5))) ∨ p2)))))) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172259855695524968226355298052 : ((((((p1 → False) → p3) ∧ (p1 → p1)) ∧ p4) ∨ ((False ∧ p1) ∨ (p2 ∨ p3))) ∨ (True ∨ (((p3 → p1) → p5) → (p5 → (p4 ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203929779191535012938543547844 : ((p2 → (((p3 ∨ p2) → False) → p5)) ∧ (((p4 → (p4 → p1)) ∨ (((p1 ∨ p1) ∧ (p4 ∧ (p4 ∧ p2))) ∧ False)) ∨ ((p3 ∨ p3) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45012627036995539740786017610 : ((((p4 ∧ p2) ∨ (p1 ∧ ((p3 ∨ p2) ∧ ((((((True ∧ (True ∨ p1)) ∨ True) ∧ p1) → p1) → (p5 → p5)) → (p1 ∨ p4))))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47658421313946686228324769649 : (((((((True ∨ ((False → False) → True)) ∧ p4) ∧ ((p1 ∨ (p2 ∧ p5)) ∨ p4)) ∧ (((True → p4) → p2) ∨ p5)) ∧ p3) → (p2 ∨ p5)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h13 =>
          -- We want to use the implication h13 based on <expert-advice>. So we show its premise.
          have h14 : (True → p4) := by
            -- Implications on the right can always be decomposed.
            intro h15
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h13, we can now drive its conclusion.
          let h16 := h13 h14
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h16
        case inr h17 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h17
      case inr h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h21 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
        case inr h22 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h19
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h24 =>
        -- We want to use the implication h24 based on <expert-advice>. So we show its premise.
        have h25 : (True → p4) := by
          -- Implications on the right can always be decomposed.
          intro h26
          -- One of the premise coincides with the conclusion.
          exact h23
        -- We have shown the premise of h24, we can now drive its conclusion.
        let h27 := h24 h25
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h28
  case inr h29 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h30 =>
      -- Disjunctions on the left can always be decomposed.
      cases h30
      case inl h31 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h32 =>
          -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
          have h33 : (True → p4) := by
            -- Implications on the right can always be decomposed.
            intro h34
            -- One of the premise coincides with the conclusion.
            exact h9
          -- We have shown the premise of h32, we can now drive its conclusion.
          let h35 := h32 h33
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h35
        case inr h36 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h36
      case inr h37 =>
        -- Conjunctions on the left can always be decomposed.
        let h38 := h37.left
        let h39 := h37.right
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h40 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
        case inr h41 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h38
    case inr h42 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h43 =>
        -- We want to use the implication h43 based on <expert-advice>. So we show its premise.
        have h44 : (True → p4) := by
          -- Implications on the right can always be decomposed.
          intro h45
          -- One of the premise coincides with the conclusion.
          exact h42
        -- We have shown the premise of h43, we can now drive its conclusion.
        let h46 := h43 h44
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h46
      case inr h47 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602740688325216445820129709633 : ((((False ∨ (p1 ∧ ((p3 → (((False ∨ p3) ∧ (p1 → (p4 ∧ (p2 ∨ True)))) ∧ p3)) ∧ ((p5 ∧ (p3 → (True ∧ p3))) ∨ False)))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349142053982911566328364403606 : (p3 → (True → (p2 → (((p4 ∨ ((p5 ∧ p5) → False)) → ((((p1 ∧ p5) ∧ p4) ∨ ((p4 ∨ p1) → (p3 ∧ (p1 → p3)))) → p5)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68441294634015941639772035733 : ((p3 → (True ∧ ((((((p4 → (p5 ∨ p1)) ∨ p2) ∨ ((p3 → p5) ∧ False)) → (p1 ∨ p1)) ∨ True) ∨ (p3 ∨ ((True → True) → True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_135038988399659495021358696684 : ((((p2 ∧ (p4 ∨ (False → (((p3 ∧ ((((p4 ∧ p4) → p3) ∨ p4) ∧ False)) → False) ∨ p5)))) ∧ False) ∨ (p4 ∨ p2)) ∨ (p1 → (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147334177029972184888919625013 : ((((((((p3 ∨ p5) ∨ (p1 → (p3 ∨ p2))) → p1) → p2) → ((True → False) → p1)) ∨ (p4 ∨ p1)) ∨ True) ∨ (p3 ∨ ((p4 → p1) ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314863767121884677776640358483 : (p3 ∨ (((p2 → (p2 → ((p4 → p5) ∧ p2))) ∧ (p3 ∨ (p5 ∨ True))) → (((p4 ∧ ((p3 ∨ (p5 ∧ p2)) ∨ p5)) ∧ True) ∨ (p5 → True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200914788943460958986279046652 : ((p1 ∨ ((((p5 ∧ p3) ∧ p3) ∧ False) → p5)) → ((((p1 ∧ ((p5 → ((p5 → p3) → (p3 ∧ (p4 → p3)))) → p2)) → True) → False) → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : ((p1 ∧ ((p5 → ((p5 → p3) → (p3 ∧ (p4 → p3)))) → p2)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h4
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : ((p1 ∧ ((p5 → ((p5 → p3) → (p3 ∧ (p4 → p3)))) → p2)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h8
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264918020603313662260334424600 : (True ∧ ((p1 ∧ p5) → (p2 ∨ ((p3 → (((p2 ∨ ((False ∨ p5) ∧ (p4 → (p1 ∧ p2)))) ∨ (False → (p3 ∨ p1))) ∧ (True → False))) ∨ p1)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159598925080694100335935439324 : (((p5 → ((p2 ∧ True) ∧ (p5 → ((p2 ∧ (p4 ∧ (p3 ∧ (p4 ∨ p5)))) → (p3 → p1))))) ∧ p5) → ((p1 ∨ ((p3 ∨ p2) ∧ p4)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681252674166513401191386992845 : ((((p4 ∧ (p5 ∨ ((((p1 ∧ False) ∧ True) → (True ∨ p4)) ∨ ((False → ((True → p2) ∨ p5)) → p5)))) → ((p2 ∧ p1) ∧ (p3 → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164451772090918872749727797065 : ((((((True ∧ (p3 ∧ p1)) ∨ p1) ∧ ((p1 ∧ p4) → ((p1 ∨ True) ∧ p3))) ∧ p3) ∧ p3) ∨ (True ∨ (p4 ∨ (((p1 → p5) ∧ True) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165111076462464512867495110207 : (((p2 → (((p1 ∧ p3) ∧ (p5 ∧ p1)) ∧ (p1 → ((False ∨ p2) ∧ (False → p4))))) → p4) ∨ ((p3 → ((True → False) → (p2 ∧ True))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62850005344593516222553777971 : ((p4 ∧ (((p4 ∨ p5) → (p1 → p5)) ∧ ((p1 ∨ ((p3 → (p2 ∨ ((p4 ∨ p1) → True))) → (p1 → ((p2 → p3) ∧ p4)))) ∨ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3010638417642444907243085279 : (((p5 → p2) ∨ False) → (((True ∧ True) ∧ (p5 ∨ (p2 ∨ ((((p5 ∨ p4) ∧ p1) ∨ ((p5 → p3) → (p1 → p3))) → p4)))) ∨ True)) := by
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
theorem thm_5_vars_104543272350515010110130028941 : ((((True → ((((p4 ∨ (p5 ∧ p5)) ∨ p3) ∨ (((p5 → False) ∨ p1) ∨ True)) ∧ (p3 ∧ (False ∧ p5)))) → p1) ∨ (p3 → p4)) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- False on the left can always be used.
  apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266240245554532873674807849477 : (True ∧ (p5 → (((((((True → ((p1 → (p1 → (p2 → p2))) → (p3 → (False ∧ p4)))) ∨ True) → p2) → p1) ∧ (p1 ∨ p1)) ∨ p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_761200967657235608805010367386 : (((p2 ∧ (p5 → ((p3 ∧ (p2 ∧ (p4 → (((((p5 ∧ p4) ∧ (p5 → (False ∧ p4))) ∨ p3) ∨ (True → p3)) → p3)))) → (p3 ∧ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_695905964731563714522062715172 : (((((p2 → p3) ∨ ((p1 → p4) ∨ ((((False ∧ p1) ∧ False) ∨ p1) ∨ p2))) → ((((p1 → False) → (p5 ∧ p5)) ∧ p2) → (p5 ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60702645834444734810250407875 : ((True ∧ (((((True → p5) → p1) → p3) ∧ (False ∧ p1)) ∧ ((p4 ∨ ((p2 → (p2 ∨ p4)) → (p5 ∨ (p3 ∨ p1)))) ∨ (p2 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704528035139240339946681329084 : (((((p1 → p4) ∧ ((((True ∧ False) ∧ p4) ∧ p5) → p3)) → (p3 ∨ ((True ∨ (False → ((p3 ∨ False) → False))) ∨ (p4 ∨ (False ∧ p5))))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135367827152574483145968400027 : (((((p4 ∧ (True → ((False ∨ (p1 → (p2 ∨ p2))) ∨ ((True ∨ False) ∨ p1)))) → False) ∧ True) ∨ (False ∨ (p5 ∧ p5))) ∨ ((True ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49916615962324822799871501607 : (((((p3 ∨ (((p5 ∧ p4) ∨ p1) ∨ (p1 ∨ ((p1 ∧ p3) → p3)))) ∨ (True ∧ (True → p3))) → p4) ∧ ((False → p3) ∧ (True ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184727619408815470470146654723 : (((False → ((False → (p2 ∨ False)) ∧ p4)) → ((False ∧ p1) ∨ p2)) ∨ ((False → (p3 → p2)) ∨ ((p1 → (p3 ∨ (p1 ∧ p2))) → (p2 → p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328705533418535656435026204755 : (True → (((((p5 ∧ p2) ∧ True) ∧ p5) ∨ (((p4 ∨ p2) ∧ True) ∨ True)) ∨ (p5 ∨ ((((p2 ∧ (p3 → (p3 ∨ p1))) ∨ p5) ∧ True) ∨ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164429286084130594571034598458 : ((p5 → ((p2 ∧ p5) ∨ (False ∨ (False → (p5 ∧ (False ∨ (((p4 → p4) → p3) ∨ p1))))))) ∧ ((p1 ∧ (p3 → False)) ∨ (False → (True ∨ p3)))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251318166555185642771196558135 : ((p2 → p3) ∨ ((((((True ∧ p4) ∨ (p2 ∨ p1)) ∨ False) ∧ p1) → p3) → (p3 ∨ (((p1 ∨ (p1 ∧ p2)) ∨ (p3 → True)) ∨ (True → p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53359924718403254109418290499 : (((((p3 → (p4 ∧ (p3 ∨ p1))) ∨ (p1 → (False ∧ p2))) ∨ p3) → (False ∧ (p2 → (((False → p3) ∧ ((p3 → p2) → p2)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133978574772625004502796108741 : (((((((p1 ∨ (p4 ∨ (p5 → ((p5 ∨ p5) ∨ (p2 ∨ p1))))) ∧ p3) ∧ (p5 ∧ (p4 ∨ p1))) ∨ False) ∧ p3) ∨ True) ∨ (p5 → (p5 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668375546838834898031611477828 : (((((((((p4 ∨ ((p4 ∨ ((p4 → p2) → p4)) → (True ∧ p5))) → p3) ∨ (p4 ∨ True)) ∧ False) ∧ p2) ∧ p4) ∨ (True ∨ (p1 ∧ False))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114422216318279583323628217255 : ((((p5 → p2) → (False ∨ ((p4 → ((((True → True) ∨ (p5 → p1)) ∧ p1) ∨ p5)) ∨ p2))) ∨ ((p3 ∧ (p1 ∨ p2)) ∨ p4)) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_630217611282857475732534462594 : ((((((p1 ∧ p1) → ((((p2 ∧ (p5 → (p5 → ((p3 → p2) ∧ (((True → True) → p5) → p5))))) ∨ p1) ∧ p2) ∨ False)) ∨ p2) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161869231471379813933261627776 : ((False → (((((False ∨ (p4 → p5)) ∨ ((((True ∨ True) ∧ False) → p2) → True)) → p3) ∨ p5) → p1)) → ((p1 ∧ (p5 ∧ p5)) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47121057315676034400865573324 : ((((p3 → ((p2 ∨ ((((p1 → (True ∨ ((p4 ∧ p4) → False))) → p4) ∨ True) → p4)) ∧ p1)) ∨ (True ∧ (p5 ∨ p3))) ∨ (p5 → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314859623304861954089122276483 : (p3 ∨ (((p5 ∧ ((((True ∨ (False → True)) → p4) ∧ True) ∨ p3)) → p3) → (((True ∨ True) → (p4 → p4)) ∧ ((p3 ∨ p1) ∨ (False → p5))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257257436952844301836021100511 : ((p2 ∨ p3) → ((((p5 ∨ ((True → ((p5 → p5) ∧ p1)) ∨ (p2 ∨ p3))) ∨ (False ∨ (p5 → p4))) → (p5 ∨ (p1 ∨ True))) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164923655150043475942282962568 : (((((p4 ∨ (((p1 → ((p4 ∨ False) ∧ p1)) ∧ (p4 ∧ p5)) → p2)) → p4) ∨ True) → p1) ∨ ((False → ((False ∧ False) ∨ p5)) → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_20245943828878899643827220220 : ((((p4 ∨ (p4 ∨ (p2 ∧ p4))) ∧ (p3 ∨ (((False ∧ p3) ∨ p5) → p5))) ∨ ((p1 ∧ p1) ∨ (((p4 ∧ p4) ∧ (p2 ∧ p4)) → p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h6 := h3.left
  let h7 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314733876166870623270532826233 : (p3 ∨ ((((p2 ∧ (p3 ∨ ((p2 ∨ p4) ∧ (p3 ∧ False)))) ∨ (False ∨ p2)) ∧ p3) ∨ (((p1 → ((p1 → p1) ∧ True)) ∨ (p5 → p3)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113883264290489593980609765361 : ((((((p3 ∧ p1) → ((((p2 → (p4 ∨ p2)) ∨ (p1 ∨ p1)) ∧ p1) ∧ (True ∧ p5))) ∧ False) ∨ True) ∧ (p4 ∨ (p2 ∨ False))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738252708601156713411319413443 : ((((False ∧ p4) ∨ (False ∧ (True → (((p2 ∨ ((False ∧ (p1 ∧ (False ∧ True))) → ((((p1 → p5) ∧ p3) ∧ p1) → p5))) ∧ p4) ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64174369549147376945411129137 : ((False ∨ ((p1 → False) ∨ (p4 ∨ ((False ∨ p3) → ((p5 ∧ (((p4 ∨ (p1 ∧ (p4 ∨ ((p4 → p5) → p4)))) ∨ p5) ∨ p3)) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



