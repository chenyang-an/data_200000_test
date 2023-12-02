variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180682764844818486516459656764 : ((((True ∧ p4) → (p4 ∨ (p3 → p4))) → ((False ∨ (p1 ∧ p2)) ∧ True)) → (((False ∨ p3) ∧ ((p1 ∧ p2) ∧ (p2 ∧ False))) ∨ (p3 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133681577285837153203381738261 : ((((((p2 → p2) ∧ ((p2 ∨ True) ∨ (p2 ∨ p4))) → (((p2 ∧ p5) ∨ p4) → False)) ∧ (True ∨ (True ∧ p5))) ∧ True) ∨ (True ∨ (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123148905121997262459712142282 : ((((False ∧ True) → ((p5 ∨ (True → (p2 → p1))) ∨ ((((p3 ∧ (p4 ∧ False)) ∧ True) ∧ False) → p3))) → (p2 ∧ (p5 ∧ False))) → (False ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ True) → ((p5 ∨ (True → (p2 → p1))) ∨ ((((p3 ∧ (p4 ∧ False)) ∧ True) ∧ False) → p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653865891251220348520352911861 : ((((((False ∧ (False ∨ (p4 ∧ p3))) ∧ (((False → p1) → ((p2 ∨ (p1 → p3)) → p1)) → ((False ∨ True) ∧ p1))) ∧ p3) ∨ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232369064954323003132522993673 : (((p4 → p5) → p3) → (p5 → ((True ∧ (((False ∨ (p1 ∧ (((p1 → p4) ∨ False) ∧ ((p1 ∧ p2) ∨ (p3 → p4))))) → p3) → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178276597367298605255679870085 : ((((p5 ∨ False) ∧ (False ∧ (p1 → (p2 → (False ∧ p1))))) ∧ (p4 → False)) ∨ (p2 → ((p1 → ((p1 ∨ (p4 ∨ p5)) ∧ (p2 ∨ p4))) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300689851305006434467664498183 : (False ∨ ((p2 ∧ ((p3 → ((((False ∨ p4) → p2) → p1) ∨ p2)) ∨ ((True ∧ (False ∧ p3)) ∧ p5))) ∨ (((False → p1) → (True ∨ True)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53929636140950347230823591592 : (((p5 ∨ ((p3 ∨ ((p3 ∨ p3) ∨ p4)) ∨ (p5 → True))) ∨ ((((p5 → ((((False ∧ p3) ∧ p2) ∨ False) → False)) ∨ True) ∨ p1) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84102444078225971301191862731 : (((((p3 → p2) ∨ p4) ∨ (((p5 ∨ (p1 ∨ p4)) ∨ (p4 ∨ (p5 → p4))) → p5)) ∧ (((p5 → p4) → False) ∧ (p4 ∧ (p1 → True)))) → p2) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h6 := h3.left
      let h7 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h10 : (p5 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h8
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h12 := h6 h10
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h3.left
      let h15 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h18 : (p5 → p4) := by
        -- Implications on the right can always be decomposed.
        intro h19
        -- One of the premise coincides with the conclusion.
        exact h16
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h20 := h14 h18
      -- False on the left can always be used.
      apply False.elim h20
  case inr h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h3.left
    let h23 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h24 := h23.left
    let h25 := h23.right
    -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
    have h26 : (p5 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h27
      -- One of the premise coincides with the conclusion.
      exact h24
    -- We have shown the premise of h22, we can now drive its conclusion.
    let h28 := h22 h26
    -- False on the left can always be used.
    apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323801125353631441510965737708 : (p5 ∨ (((p4 → p5) ∧ (((p4 → ((p1 ∨ (True → p3)) → (False ∨ p3))) ∧ p3) ∧ (True → False))) ∨ (False → (p5 ∧ ((p4 ∨ p2) ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_319090901292256471267238092510 : (p4 ∨ (((((((p3 ∧ p3) ∨ (p5 ∧ p1)) ∧ p5) ∨ True) → p3) ∧ (p2 → (False ∧ ((p4 → p2) → p1)))) → (p4 → ((True → p5) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : ((((p3 ∧ p3) ∨ (p5 ∧ p1)) ∧ p5) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52550328184707931754455608651 : (((((p3 → ((p1 ∧ (False ∧ p1)) ∧ p2)) ∧ (p2 ∧ (p1 → p5))) → p1) ∨ ((False → p3) ∧ ((True ∨ p5) ∧ ((p1 → True) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694012031644152849188185846487 : ((((((p3 → (True → (p4 ∧ True))) ∨ (False ∧ (False ∧ p4))) → (p4 ∨ p2)) ∨ (((p5 ∧ (p1 ∨ ((p1 ∨ True) → p1))) ∧ p1) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137984518055367331448590672392 : ((p5 ∨ ((False ∧ False) ∨ ((p2 → p4) → (((p2 ∧ (True → ((p4 ∧ True) → p4))) ∨ p2) ∧ ((p3 ∨ False) → p3))))) ∨ ((True ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223877837741077273031361254038 : ((p3 ∨ (False → p3)) ∧ ((p2 ∨ ((p2 ∧ p2) → p3)) → (((p4 → p1) ∨ p3) → (((p3 ∧ (p4 → ((p4 → p5) → p2))) → p4) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67645680485110924497897587667 : ((p1 → (p2 ∨ (((p2 ∨ (p3 ∨ (((p2 ∧ True) ∧ p4) ∧ ((((p4 ∧ p3) ∧ (p5 → False)) ∨ False) ∨ p5)))) → (False ∨ p2)) ∨ p1))) ∨ p3) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802498471520346546040717388046 : (((p2 → (p3 ∨ ((((p5 ∧ p1) ∨ (((False → ((p3 → True) ∨ (p2 ∧ p5))) ∨ p1) → (p3 → p1))) ∨ (p2 → (p4 → p3))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53802283774578960161817161235 : (((((p5 → p4) ∨ (((p2 ∧ True) ∧ p2) ∨ p5)) → p2) ∨ ((((p3 → p4) → ((False ∨ (p1 ∨ (p5 ∧ False))) → True)) → p3) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112216598136870944690940505182 : (((False ∨ (p4 → (True ∧ ((((True → (p3 ∨ ((p2 ∨ p2) → False))) ∨ p3) ∧ p5) → (p5 ∧ (p2 ∨ (p1 ∨ p4))))))) ∨ True) ∨ (False ∨ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231001166954696902264969434508 : (((p5 ∧ False) ∨ p2) → (((((False ∨ p4) → p2) ∧ p1) ∨ ((True ∧ ((True → (((p5 → (p5 ∨ p1)) ∧ p2) ∧ p4)) ∨ p4)) → p4)) ∨ p2)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52157196759227951812554601454 : ((((p5 → (((p1 ∨ (p4 ∨ p1)) → p4) → (p2 ∧ False))) ∨ (p4 ∧ (p4 ∨ False))) → (((True ∨ (p5 ∨ p3)) ∧ (p5 ∨ p5)) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42642628035716140355156399694 : (((p3 ∨ (p4 → (p2 → (p2 → (p2 → ((((p2 ∧ ((p4 ∧ ((p2 → p5) ∨ p1)) ∨ (True ∧ False))) → p3) → True) → p5)))))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48006255820747159611317015402 : ((((((p2 ∨ (True → p2)) ∨ p5) ∧ (((p4 → p5) ∧ (p4 → p3)) ∧ p2)) → ((False → (p3 ∨ p5)) ∨ (p1 ∧ p4))) → (p4 → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147417636464302144263914290674 : ((((False ∨ (p3 → (False → p1))) → (p3 → ((p4 ∨ p1) ∧ ((p1 → p2) ∧ (p2 ∧ (p4 ∨ p5)))))) ∨ p3) ∨ ((p1 ∨ (p4 ∧ False)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703313775099455091813447396512 : ((((p5 ∧ (((p5 ∧ p2) ∧ (p2 ∧ True)) ∧ (False ∧ p2))) ∨ (False → ((p3 ∨ p2) ∨ (p3 ∧ (False ∧ ((p5 → p2) ∨ (p5 → True))))))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_319446502300839714275579720575 : (p4 ∨ ((((p2 ∨ (p5 → (True ∧ p3))) ∨ ((False ∧ p5) ∨ p2)) ∧ p2) ∨ (((p5 ∧ p3) ∧ p3) ∨ ((p3 ∨ (True ∨ (p3 ∧ p3))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351909292904637465270979148056 : (p4 → (((((p1 → p4) ∧ p2) ∨ p1) → ((p3 → p4) ∧ p1)) ∨ (p2 ∨ ((p2 ∨ (False ∧ True)) ∨ ((p4 → True) ∧ ((p4 ∧ p4) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191193943926692297719447367817 : ((((p5 → p5) ∧ True) → ((p3 ∨ p3) ∨ (p2 → p3))) ∨ (p5 → ((((p3 ∧ False) ∧ p5) ∨ p5) ∧ ((p3 → (p2 ∨ (False ∧ False))) → p5)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356643940349651258476291748953 : (p5 → (((((p1 ∧ p3) ∧ (p1 ∨ True)) → p4) ∧ p5) → ((p4 → (p1 ∧ p4)) → (((p1 → False) ∨ (False ∨ (p5 ∨ False))) ∧ (True ∨ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46808836965106054496412610028 : ((((((((p2 → p2) ∨ True) ∧ (((p1 → ((p5 → (p4 ∨ False)) ∨ p4)) ∨ (p4 ∧ p5)) ∧ p4)) → p3) ∨ p2) ∧ p5) ∨ (True ∨ p3)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256484864143541720309020630882 : ((False ∨ p4) → (((True → (True → p4)) ∨ p3) → (((((p4 ∧ p4) ∨ p5) ∨ p2) ∨ p3) → (p5 ∨ (((p1 ∧ (p1 ∨ p2)) → True) ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h10 =>
            -- False on the left can always be used.
            apply False.elim h10
          case inr h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h12
            -- True on the right can always be proven directly.
            apply True.intro
        case inr h13 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h14 =>
            -- False on the left can always be used.
            apply False.elim h14
          case inr h15 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h16
            -- True on the right can always be proven directly.
            apply True.intro
      case inr h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h2
        case inl h18 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h19 =>
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h1
          case inl h22 =>
            -- False on the left can always be used.
            apply False.elim h22
          case inr h23 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h17
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h26 =>
          -- False on the left can always be used.
          apply False.elim h26
        case inr h27 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h28
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h29 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h30 =>
          -- False on the left can always be used.
          apply False.elim h30
        case inr h31 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Implications on the right can always be decomposed.
          intro h32
          -- True on the right can always be proven directly.
          apply True.intro
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h35 =>
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h37
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h39 =>
        -- False on the left can always be used.
        apply False.elim h39
      case inr h40 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h41
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156619111211624723180833095028 : (((((p3 → (p3 ∧ (False ∧ (p4 ∧ (((False ∨ p2) ∧ (False ∨ True)) ∨ p1))))) ∧ p3) ∨ False) ∧ p1) ∨ (True → ((p4 → p4) ∧ (True ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614351769019287941065138608404 : (((((True ∧ ((((p3 ∧ (p5 ∧ (p4 ∧ (p3 → p1)))) ∧ (p1 ∨ p5)) → p5) → ((p4 ∧ True) → False))) → (p1 ∧ (p2 ∨ p4))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_117060974164457376177266100300 : (((p5 ∨ p2) → ((p1 ∨ p2) → ((p2 ∧ p4) → ((((p2 ∨ p3) ∧ ((True → (p2 ∨ (p1 ∧ p3))) → p1)) ∧ p3) ∨ p2)))) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h2
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112649536396889223922025003667 : ((((((p1 ∨ (p3 ∧ ((False ∧ (p2 ∧ (p2 ∨ (True ∧ False)))) → p2))) ∧ p4) ∧ (False → True)) ∧ (p3 ∧ (p3 ∧ p5))) → p2) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49220604800412843986340671569 : ((((p1 → p5) ∧ (((((p2 ∧ p4) ∨ ((True → (p1 ∨ False)) ∨ (p4 ∧ False))) → True) → p1) ∨ (p3 ∨ p4))) ∨ ((True → True) → True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171592287191698722200169353918 : ((((p3 ∨ ((p2 ∨ (p1 ∨ (p1 → True))) ∧ p5)) ∨ (p1 ∨ (p5 ∨ p1))) ∨ p3) ∨ (True ∧ ((p1 ∧ ((p1 → p4) ∧ True)) → (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711601448371866674001314657296 : ((((p2 → ((p3 ∧ True) ∧ (p5 ∨ p3))) ∧ ((((p2 → True) ∧ ((p4 ∧ ((p4 → True) → p2)) ∨ False)) ∧ p2) ∨ ((p1 → p4) → True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627531310579417319413932799296 : ((((((p5 ∨ ((p5 ∨ (p4 ∨ True)) → (((p3 ∧ ((p2 ∨ p1) → ((True ∧ p4) ∧ p2))) ∨ p1) ∨ p3))) ∧ (p4 → p3)) ∧ p4) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232348573203866659736397984445 : (((p4 → p2) → True) → ((True → (p3 ∧ ((p2 → ((False ∧ p3) → p4)) → (p4 ∧ p5)))) ∨ (p5 → (p5 → ((p1 → p1) ∧ (p5 ∨ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217164165545778905612914044387 : ((((p1 ∧ True) → p2) ∨ p3) → ((False ∧ ((p3 ∧ ((p1 ∧ True) ∨ (True → p1))) → p5)) ∨ ((p4 ∨ (p2 ∧ p1)) → ((p3 ∧ p3) → True)))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115315148471194932704667562012 : ((((p4 ∨ ((False → p4) → p2)) ∨ ((False ∨ False) → p3)) → (p1 → (p3 ∨ (((p1 → ((p1 → True) ∧ True)) → p4) ∧ p5)))) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2317192173410727314797015046 : (((p3 ∧ (p5 → p3)) → (p2 ∧ (((p2 ∨ p1) ∨ (p3 → p2)) ∨ p4))) → ((p1 ∨ p5) ∨ ((False ∧ ((False ∧ p4) ∨ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135808162082116140417551535277 : (((p1 → ((((True → p5) ∨ True) ∧ (False ∨ (True ∨ (p1 → p5)))) ∧ False)) → (p5 → ((p2 ∨ (p5 ∧ p4)) ∨ p1))) ∨ (p3 → (False → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347184066904869319765153359209 : (p3 → ((((((p5 → p3) ∧ ((p1 → True) ∨ p4)) ∨ p2) → p4) ∧ False) ∨ (p2 → (((((p4 → p4) ∨ False) ∨ (p5 ∨ p5)) → p2) ∨ True)))) := by
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
theorem thm_5_vars_719740207844894043594399639873 : ((((p1 → ((p2 ∨ False) ∧ False)) ∨ ((((p2 ∨ p4) ∧ (p3 ∨ (p3 ∨ False))) ∨ ((False ∨ (((p4 ∨ p1) ∧ False) ∨ False)) → True)) ∨ p5)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227091868249217154841174910814 : (((p3 ∨ p5) → False) ∨ (((p3 ∧ p5) ∨ p5) ∨ (False → ((p5 → ((False → (((True ∨ p1) → (False ∧ p3)) ∨ False)) ∨ (p3 ∧ True))) ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_632463881230083567993549336983 : (((((p2 ∨ ((p2 ∧ (p2 ∨ (p4 ∧ False))) → ((p1 ∧ ((((p1 ∨ False) ∨ p5) → (False ∧ (p4 ∨ p4))) ∨ False)) ∨ p4))) → p1) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42722132769117521039370827837 : (((True → ((((True → p3) ∨ (((p2 ∧ ((p5 → (p4 ∧ p2)) ∨ p3)) → (p2 ∨ (p3 → p1))) → (False ∨ p4))) ∧ p4) ∧ True)) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2557040684184687353472188644 : (((True → (p1 → p3)) → ((p4 ∨ p1) ∨ p4)) ∨ (((p5 → ((p2 ∨ False) → True)) ∧ ((p1 → p1) ∨ p2)) ∨ (True ∧ (p5 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305420111061307223964964344493 : (p1 ∨ ((p3 ∨ (p2 → (((p2 → (False ∧ (p2 → (True → True)))) ∧ (p1 → p5)) → False))) ∨ (((True → (False → p4)) → p3) ∨ (False ∨ p3)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48513277232848824934987113455 : (((((p4 ∨ (p3 ∨ ((p4 → (True ∧ p3)) ∨ (((p4 ∨ p5) ∧ p2) ∧ p1)))) ∧ (True → (p1 ∨ p4))) ∨ p4) ∧ (True → (p4 ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49263887961010273126053807081 : (((p1 ∧ ((p3 → ((p3 → p4) → False)) ∧ ((False ∧ p2) ∨ ((p5 ∨ p3) → (((p5 ∨ p5) → p3) → p4))))) ∨ ((p4 ∧ p2) → p4)) ∨ p3) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_800596035295169309082226290090 : (((p2 → ((((p1 ∨ p3) ∨ ((p5 → (p4 → (p1 ∧ p1))) ∨ (p2 ∨ p2))) → ((True ∧ ((p3 ∧ p1) ∨ (False → p3))) ∧ p4)) → p4)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 ∨ p3) ∨ ((p5 → (p4 → (p1 ∧ p1))) ∨ (p2 ∨ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147484774540608085620492613075 : (((p4 ∧ ((((True ∧ ((False ∧ True) ∨ True)) → ((p5 ∧ (p3 → p4)) ∨ p1)) → (p1 → p5)) → p3)) ∨ True) ∨ (False → (p5 → (p5 ∧ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55446523321138138803522651192 : (((((p1 ∨ p3) ∨ (p3 → True)) → p1) → (((p5 ∨ p1) ∨ (p1 ∨ p5)) → (p5 → ((p5 → ((p5 ∨ (p4 ∨ False)) ∧ p2)) ∨ p1)))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h6 : ((p1 ∨ p3) ∨ (p3 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h8 := h1 h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h11
    case inr h12 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h13 : ((p1 ∨ p3) ∨ (p3 → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h13
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_77957299157691328739368661660 : (((p3 ∨ (((((((True → p2) ∧ p1) ∨ (False ∨ (p5 → p3))) ∨ p1) ∨ (p3 ∧ p4)) ∨ p2) ∨ (((p1 ∧ p3) ∧ p4) → p4))) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ (((((((True → p2) ∧ p1) ∨ (False ∨ (p5 → p3))) ∨ p1) ∨ (p3 ∧ p4)) ∨ p2) ∨ (((p1 ∧ p3) ∧ p4) → p4))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75697174574241915596940161689 : ((((((((p2 → p4) → ((p5 → True) → (p4 → (False → p3)))) ∧ p4) ∧ ((p2 ∨ ((p3 ∨ p3) ∨ p4)) → p3)) → p4) ∨ p5) → False) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((((p2 → p4) → ((p5 → True) → (p4 → (False → p3)))) ∧ p4) ∧ ((p2 ∨ ((p3 ∨ p3) ∨ p4)) → p3)) → p4) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135390735273085833359992281422 : (((((True ∧ (p3 ∧ (False ∧ False))) ∨ (p2 ∧ ((p2 ∨ (True ∧ p1)) ∨ p1))) ∨ (True ∨ False)) ∨ (p3 ∧ (p5 → False))) ∨ ((p1 → True) → p5)) := by
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
theorem thm_5_vars_52265468216797223568301144373 : (((p5 ∨ ((p3 ∨ (((p5 → False) ∧ p1) ∨ p1)) → ((p5 → (True → p4)) ∨ p5))) → (True ∧ ((p1 → False) ∧ ((p1 ∨ p4) ∨ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_618898619650767596732428128432 : (((((p1 → (p3 → True)) ∧ (p1 ∧ (((p5 → False) ∨ (((p5 ∨ ((True ∨ p2) ∧ True)) → p2) ∧ True)) → (True ∧ (p3 ∨ p4))))) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_358583337771675011962374658443 : (p5 → (p3 → ((p2 ∧ (((p1 ∧ (False ∨ ((((p5 → False) ∧ p1) → (True ∧ False)) ∨ (p5 ∨ (p1 ∨ p2))))) ∨ (False ∧ p1)) ∨ p3)) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40799643122271840736973107323 : ((((True ∨ (p2 ∧ (((False → (p5 ∨ (p5 ∨ (((p4 ∧ p5) ∨ p2) ∨ (p1 ∧ True))))) ∧ (p2 ∧ p4)) → (True → p2)))) → p4) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64658963499891677728526267280 : ((p1 ∨ (False ∨ ((p5 ∨ ((p1 ∨ (False ∧ p3)) ∧ ((True ∨ p3) → (p2 ∨ ((p4 → p4) → (p4 ∨ (True ∧ (False ∨ False)))))))) ∨ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314649460157528876597928598847 : (p3 ∨ (((((p2 ∨ (p4 ∧ (p5 → p2))) ∧ (p3 ∨ (p5 ∧ p1))) ∨ True) → (p4 ∧ p4)) ∨ (((False ∧ p1) → p2) ∨ (p4 ∧ (p5 ∧ False))))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61635072820498305954777260456 : ((p1 ∧ ((p1 → p5) → ((p5 ∨ ((((True ∧ (p2 → p5)) ∨ True) ∧ (((p2 ∧ p4) ∧ (p1 ∧ (p1 ∨ p5))) → False)) ∨ p4)) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157912184381796112960895149706 : ((((p3 ∨ p1) ∧ (p5 → ((p1 → p4) ∧ (p2 → p2)))) → (((p4 → True) → p1) ∧ (p4 ∨ p2))) ∨ (True ∨ ((p4 ∨ p5) ∧ (True ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119295421434935836758290051998 : ((p3 → (((((p3 → ((p1 → (p3 → True)) ∧ (False ∧ True))) → (p3 ∧ True)) ∧ p4) ∧ ((p2 ∨ (p1 → True)) ∨ p2)) → p1)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684717159779830108662722625718 : (((((p5 ∧ p5) ∧ (p2 ∧ (((p1 ∧ (((p3 → p3) ∨ p5) → p1)) ∨ (p4 ∨ p3)) ∧ p2))) ∨ (((False ∨ p1) → False) → (p2 → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231323432625732796455463060144 : (((True → p1) ∨ p4) → ((((p2 ∧ True) ∧ True) ∨ ((p3 → (p1 ∧ True)) → (True → (((p4 → p4) ∧ (p3 ∧ True)) ∨ False)))) ∨ (False → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168326118588104457118976820185 : (((p3 → p1) ∧ (((True ∧ (p1 ∧ True)) ∧ (((True → False) ∨ p3) ∨ (p3 ∨ p4))) ∧ p1)) → ((p4 → False) ∨ ((p1 ∨ (p1 ∧ p4)) → True))) := by
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
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
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
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h20 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597827744026782824104543415443 : ((((((True → False) ∧ p5) ∧ ((True → ((p4 ∨ (((p5 → (p2 → p2)) ∨ ((p5 ∨ p5) ∧ True)) ∧ p2)) ∧ p4)) → (p2 → False))) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49018458965105694351347392766 : (((((((p1 → (p4 ∧ (p5 ∨ ((p2 ∨ p4) ∨ True)))) ∨ False) → (p1 ∧ (p4 → True))) → (False ∧ p4)) → False) ∨ ((p2 → p3) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49082960654193792076683725538 : ((((True → (((p5 ∧ (p5 ∨ False)) ∧ False) ∨ ((p2 → False) → (False ∨ (False ∧ (p3 ∨ True)))))) → (p4 ∨ p1)) ∨ ((p4 ∧ p4) → True)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691225603977108256981510863725 : (((((p5 → (p4 ∧ (p4 ∨ (p4 ∧ p2)))) → (((p2 → p2) ∧ p2) ∨ (p4 → p3))) → ((False ∧ p3) ∨ ((True → p5) → (p3 ∨ True)))) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_596759079340919024185981026562 : (((((p4 ∨ (((True ∨ False) ∨ p2) ∨ True)) ∧ ((p3 ∨ ((p1 → True) ∨ (((False ∨ True) ∨ (p4 ∨ p3)) ∧ p2))) → (p5 ∧ p3))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118223639742317495031870400652 : ((p1 ∨ ((((p1 ∧ p5) ∨ p2) ∧ (((p2 → p2) ∨ ((p1 → (True ∧ False)) ∧ ((True ∨ p3) → (False ∨ p3)))) ∧ False)) ∨ True)) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40206767973730116335665316406 : (((((p2 ∧ p3) ∨ (((p3 ∨ ((True → p5) → False)) → (p1 ∧ (True ∧ (p5 → (p1 ∨ (p1 ∨ (p4 ∨ True))))))) ∨ True)) ∧ p4) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169077071145575339009852727502 : ((p3 → (p2 ∧ ((((((False ∨ p2) ∧ p5) → p1) ∨ False) ∧ (p4 ∧ p3)) ∨ (p3 → False)))) → ((False ∨ (True → ((p2 → p5) → False))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166385000415732264861870916102 : ((False ∨ ((((((True ∧ (p4 → (False ∧ True))) ∨ p1) ∨ p4) → False) → True) → (p3 ∧ p3))) ∨ (False → (p4 → ((p2 → (True → p4)) ∧ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313048177558359687758940046246 : (p3 ∨ ((((p1 → ((False ∧ ((p5 → p5) ∧ (p3 ∨ p4))) ∨ (p4 ∨ p2))) → (p1 ∧ (((False ∨ p5) ∧ (p3 ∨ p3)) ∧ False))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118243731736278158790884930420 : ((p1 ∨ (((p1 ∧ (((False → (p2 ∨ (True ∧ True))) ∧ False) → False)) ∨ (p1 ∨ ((p5 ∧ (True → p5)) ∨ False))) ∨ (p3 ∨ p5))) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_677481500503788865427863770233 : ((((((p3 ∨ (p5 ∨ (p2 ∨ p5))) ∧ ((p5 ∨ p5) ∨ ((True → (p4 ∨ p3)) → (p4 → p4)))) ∨ p1) ∨ ((p1 → p5) ∨ (False → p5))) ∨ False) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113673977812512506598338939835 : (((((p4 ∧ (p3 ∧ p2)) → (p5 ∨ (((p2 ∨ p1) → (True → ((p4 ∧ False) ∧ (False ∧ False)))) ∨ True))) ∨ p2) → (p3 ∧ True)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299081701349973255327263221432 : (False ∨ ((((((True ∨ True) → (((p1 ∧ (p5 → p5)) ∨ ((False ∧ (p1 ∧ (p3 → (p4 ∨ False)))) ∧ True)) → False)) ∨ p4) ∧ True) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300399178839131326756062859535 : (False ∨ ((True ∧ ((((((True → p3) ∨ False) ∧ (p2 ∨ (p5 ∧ ((False → p3) ∧ False)))) ∨ p5) ∧ (p5 ∧ p5)) ∧ False)) ∨ ((p5 ∧ False) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161591754157634326735705345312 : ((True ∨ (p4 ∧ (((p3 ∨ ((p4 ∧ (p5 ∨ ((p5 → True) ∧ p2))) ∧ (p4 → p2))) ∨ p1) ∨ p2))) → (p5 ∨ (False → (p1 ∨ (False ∨ False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h10
          -- False on the left can always be used.
          apply False.elim h10
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
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h16
          case inr h17 =>
            -- Conjunctions on the left can always be decomposed.
            let h18 := h17.left
            let h19 := h17.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- Implications on the right can always be decomposed.
            intro h20
            -- False on the left can always be used.
            apply False.elim h20
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- False on the left can always be used.
        apply False.elim h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- False on the left can always be used.
      apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60404330635557470639721168965 : (((p4 → True) → (((((False ∨ p5) → False) ∨ True) ∧ p5) ∨ ((((False ∨ True) ∧ (p5 ∧ p3)) ∨ (p3 → p2)) → (p5 → (p2 ∨ True))))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h6.left
      let h10 := h6.right
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
theorem thm_5_vars_37828859870029226021253164893 : ((((p1 ∨ ((((p3 → (p3 ∨ ((((p2 → p1) ∨ False) → (True ∧ p4)) ∨ p2))) ∧ (p4 ∨ (p1 → p4))) → p5) ∨ True)) → p3) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317678025712266616538874232808 : (p4 ∨ ((((False → p3) ∧ ((p4 → (((False → ((p1 → (True ∨ True)) ∨ True)) ∧ p2) ∨ p2)) ∧ (p2 → ((True ∨ p5) ∨ p3)))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300778085288680962558401850521 : (False ∨ (((p1 → (p5 → ((p3 ∧ (False → ((p1 ∧ (p3 → p3)) ∧ p4))) ∨ p2))) → False) ∨ ((((p1 ∧ False) ∧ p5) ∨ True) ∨ (p4 ∨ False)))) := by
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
theorem thm_5_vars_160077175028786519831590121985 : (((False ∨ (((p2 → ((((False ∨ True) → p4) ∨ p3) ∨ p3)) ∧ (True → (False ∨ p1))) ∨ p1)) → False) → ((p5 ∨ ((p3 → p2) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776258892566948932549487763845 : (((p1 ∨ ((((p1 ∧ (p1 ∧ p2)) ∨ (p3 ∨ True)) → (((((p5 ∧ False) → p2) → (p3 → ((p3 → p5) → p4))) → True) → p1)) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117429660093273762260091946640 : ((p1 ∧ ((p4 ∨ (True ∧ (p1 → (p5 ∧ (((p2 → p4) ∧ (p2 → (False ∨ p4))) ∨ p2))))) ∨ ((p4 ∧ p2) ∨ (p4 ∨ True)))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613232793821699497814068714321 : ((((((((p1 ∨ p2) ∨ (p1 → ((p2 ∨ p4) ∨ (p4 → p4)))) ∨ True) → (False ∧ ((False ∧ (p4 ∧ False)) ∨ p2))) → (p3 ∨ p3)) ∨ False) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 ∨ p2) ∨ (p1 → ((p2 ∨ p4) ∨ (p4 → p4)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136240550305908017162085482250 : ((((p4 ∨ p3) → ((p2 ∨ p4) ∧ p4)) ∨ (((((((True → True) → p4) ∧ p5) ∧ p4) ∧ (p4 ∨ True)) ∧ p1) ∨ True)) ∨ ((p5 → p2) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302812173998209818675550991450 : (False ∨ (p5 ∨ ((((p2 → (p1 → p5)) → (p1 → (p1 ∧ ((p3 → p4) ∧ (((True ∧ p2) ∨ p5) ∧ p5))))) ∨ (p5 ∧ p2)) ∨ (False → p3)))) := by
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
theorem thm_5_vars_113413351340566577559954127436 : (((((((p2 ∨ (True → (p1 ∨ p1))) → ((p3 → p2) ∨ (p2 ∧ (p1 ∧ p4)))) ∧ p2) ∧ (p3 ∧ p1)) ∧ p1) ∨ (p4 → p4)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52446148098977480683550479870 : (((p2 ∧ (((p5 → (p5 ∨ p3)) ∨ ((p3 ∧ (p2 → p4)) → True)) → False)) ∧ (False ∨ (p5 ∧ (p2 ∧ (True ∧ ((p3 ∨ True) ∨ False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119468784305315331016294824919 : ((p4 → ((p5 → p3) ∨ ((p1 ∨ (((p3 → ((False ∧ (((p1 → p5) ∧ p2) ∧ False)) ∨ p2)) ∨ (p2 ∧ p4)) ∧ p2)) ∧ p3))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



