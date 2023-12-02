variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609467725379973253025233070657 : (((((False ∧ (((False ∨ (False ∧ (p1 ∨ ((p3 ∨ p4) ∧ (((p2 ∨ p2) ∨ p1) → p4))))) ∧ p5) ∧ ((p2 ∨ True) ∧ False))) ∨ p4) ∨ True) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_136037641559127820945010780339 : (((p2 ∧ ((p1 ∧ (True ∨ p1)) ∨ (p5 → (p1 ∧ False)))) → (((p5 ∨ (((p3 ∨ p5) → True) ∨ p5)) ∧ False) ∧ p3)) ∨ (False ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192167294861030655253742749027 : ((((True ∨ (((p3 ∧ p2) → False) → p4)) ∧ p2) ∧ p2) → ((False ∧ ((False ∨ (False ∧ (False → p4))) ∧ True)) ∨ ((False ∧ (True → p3)) ∨ p2))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116351442570579414039561322246 : ((((p3 ∨ True) ∨ p2) → (((p3 → p1) ∨ (p5 → ((p5 ∧ (((p4 → p5) ∨ (p1 ∨ (True ∨ p4))) ∧ p3)) ∨ p2))) ∧ p2)) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893757835616004337502070064742 : (((((True ∨ p2) ∧ ((p2 → p5) → (p5 → ((False ∧ p1) ∧ (True ∨ (((p3 → p5) ∨ p1) ∧ (p4 → p2))))))) ∧ (p5 ∧ (p2 → p3))) → False) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h3.left
    let h8 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h9
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h12 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h13 := h11 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h19 : (p2 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h20
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h21 := h5 h19
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h17
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h23 := h21 h22
    -- We need to get the left conjuct of h23 based on <expert-advice>.
    let h24 := h23.left
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187088667095364997247538401154 : (((p2 → p2) ∧ (p2 ∨ (p5 → ((p1 ∧ p2) → (False ∧ p2))))) → ((p2 ∨ (p4 → True)) ∧ (p5 → ((p1 ∨ p1) ∨ (False → (p1 ∧ p5)))))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h9
  case inl h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h11
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h13
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328904018319353016424773339571 : (True → ((p4 → (p2 ∨ (p2 ∨ (p1 ∧ (False → p5))))) ∨ (((False ∧ (p1 ∧ True)) ∨ True) ∨ ((p1 ∧ (((p4 ∧ False) ∧ p4) ∧ True)) ∧ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116838177089159723285736345273 : (((True → p1) ∨ (((p2 → ((False ∨ (((p3 → ((p3 ∨ (p1 ∨ p1)) → (p1 ∧ p4))) → p5) ∨ p1)) ∨ p2)) ∧ p5) → p4)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_311000365693508776097950906628 : (p2 ∨ ((p3 → p3) ∧ (((True ∨ (True → (((p4 ∧ p1) ∧ (p3 ∧ p4)) → p5))) ∧ (p1 → p4)) → ((p5 ∨ ((p1 → True) ∨ p5)) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154916296916603674780164715172 : (((((True ∧ ((p3 ∨ p3) ∧ p3)) ∧ (p4 ∧ (p2 ∨ p5))) ∨ (True ∧ True)) ∨ ((p4 ∨ p1) ∧ p2)) ∧ ((p3 ∨ (True ∨ p5)) → (p1 → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255739754325598898441415214613 : ((True ∨ True) → ((p1 ∧ (p5 ∨ ((p3 → ((p1 ∧ ((((p2 → p1) → (p3 ∨ p5)) ∧ True) ∨ False)) → p3)) ∧ (True → p1)))) ∨ (p5 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191050118429253482916716666887 : ((((p4 ∨ p3) ∨ (p4 → False)) → (p5 ∨ (p1 → p4))) ∨ (False → ((p1 ∧ (True ∨ ((False ∧ (p2 ∨ p4)) ∨ (True → p1)))) ∧ (p5 ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243401602266432411165225767104 : ((p5 → True) ∧ (((p4 ∨ True) → ((p4 → (((p5 ∧ (((p5 ∨ p1) ∨ True) → False)) ∨ p2) → (p3 ∧ False))) ∨ ((p4 ∧ False) ∨ True))) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134127223103123971014278971299 : ((((p5 ∨ ((((p5 ∨ p2) ∧ (False ∨ (p5 → (((p5 ∨ False) ∨ False) → p3)))) ∧ p4) ∧ p4)) ∨ (True ∨ True)) ∨ p4) ∨ ((False ∨ p3) ∧ p4)) := by
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
theorem thm_5_vars_52554340661051313880128753076 : (((((True → p4) ∧ ((p2 ∧ (True ∧ (p5 → (False → p5)))) ∨ p3)) → p3) ∨ (((p3 → p5) ∧ (False → (p2 ∨ p3))) ∨ (True ∨ p1))) ∨ p5) := by
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
theorem thm_5_vars_790833080812161731639499828064 : (((p5 ∨ (p2 → ((p4 ∧ ((False ∧ ((p3 → (((True ∨ False) → p2) → (p4 ∧ ((p4 ∨ p3) → (p2 ∨ False))))) ∧ p1)) ∧ p3)) ∨ True))) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_355941388730858877090937436860 : (p5 → (((False → p3) → ((((p5 → ((p4 → (True ∨ p2)) ∨ (p1 ∨ (False → p2)))) ∨ (p3 → p5)) ∨ True) ∧ p2)) → (p3 → (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232279635294059991285924155824 : (((p2 → p3) → p4) → ((p1 → p1) ∧ ((((((p4 ∨ p3) → p1) ∧ True) ∧ p2) ∧ ((p3 ∧ p3) ∨ ((p5 → (p5 → p4)) → p1))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169430616844250241863557364834 : ((((((p4 ∨ True) ∨ ((False ∨ False) ∧ (p4 ∧ p4))) ∨ p2) ∨ (p4 ∨ p5)) ∨ True) ∧ (p5 ∨ (((True ∧ False) ∧ (p3 ∨ (False ∧ True))) ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346626584398510178981505675036 : (p3 → (((p5 ∧ True) ∨ (p2 ∧ (p5 ∧ ((p1 ∨ False) ∧ (((p5 ∨ ((True ∧ p5) ∨ (True ∨ p1))) → p3) ∧ True))))) ∨ (p3 ∨ (p2 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40703372769233729170234289734 : ((((((((p4 ∧ p3) → (p5 ∧ (p4 ∧ p3))) → (False ∨ p5)) → False) ∨ ((((p1 → p4) → False) → (p3 ∧ p3)) → p1)) → p4) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161426784577954221983341848492 : ((p2 ∧ ((p2 ∧ (((p3 ∨ p1) ∨ (True → (p1 ∧ (p2 → (False ∨ p3))))) ∧ p5)) → (True → True))) → (((p3 ∨ p2) → p4) ∨ (p5 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113433758198373614704753958103 : ((((((p5 ∨ ((p4 → (((p5 ∧ p5) ∧ True) ∧ (p4 ∨ (False → p3)))) → p2)) ∨ (True ∨ True)) → False) ∨ p4) ∨ (p2 → True)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263158549830396763277850136007 : (True ∧ ((p4 ∧ ((p4 ∨ (False ∧ (((((p5 ∨ True) ∧ (p3 ∧ p4)) → p4) → (p5 ∨ True)) ∧ p4))) ∨ ((p2 ∨ p3) ∨ p2))) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_217731553649589615772299686583 : (((p2 ∧ (p2 ∧ p3)) → p1) → ((((p3 ∧ (p2 ∨ (p4 → (p3 ∨ p4)))) ∧ p1) → (p2 → (p2 ∧ p5))) ∨ (((p4 ∧ p1) → True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_735936059549697016568032145125 : ((((True → p1) ∧ (p4 ∨ (p2 ∧ (((p5 ∧ p1) ∧ (p2 ∨ (True ∧ p1))) ∨ ((p2 → p1) → ((True ∨ (p5 ∨ (False ∨ p5))) → p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193487605706415207396404686867 : (((False ∨ p2) ∨ ((p1 → (p1 → (p5 ∨ p2))) ∨ p1)) → ((((True ∧ p2) → ((True → (p3 ∨ p2)) → (p5 ∧ p3))) ∨ p3) ∨ (True ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738238999173270025291667512174 : ((((False ∧ p4) ∨ (((p5 ∧ ((p4 ∨ (p5 ∨ True)) → p2)) ∨ ((True → (p2 ∧ (p3 ∨ False))) → (False ∨ p5))) → ((p2 ∨ p1) ∨ True))) ∨ p5) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613514758391723519308247492082 : (((((p5 → (((False → p1) → ((((((True → (p1 ∧ True)) ∨ True) ∨ False) ∨ (p2 → p1)) ∨ p1) ∨ True)) ∧ p1)) → (p4 → p2)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54323819803151383230977253260 : (((p1 ∧ (((p2 ∨ p3) ∧ True) ∧ (p3 → p3))) ∧ (p4 ∧ ((p5 ∨ True) ∧ (p4 → (p1 ∨ ((p3 → p1) ∨ ((False ∨ p4) → p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253787501119194870011143500760 : ((p1 ∧ p2) → ((True → (((p2 ∧ (p5 → ((p5 → p2) → (False → (p2 ∧ (p1 ∧ (p4 → p3))))))) → ((False → p2) → False)) ∨ p2)) ∨ p1)) := by
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
theorem thm_5_vars_46808639088555053555957426917 : ((((((((((p4 → (p4 ∨ p2)) ∨ (False → False)) → (p3 ∨ (True → False))) ∨ p5) ∧ (False → p3)) → False) ∨ p2) ∧ True) ∨ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164519266561970802999926805374 : ((((p4 ∧ (False ∨ (p1 ∨ (p2 ∨ (p1 ∨ ((p1 → p4) ∧ p3)))))) ∨ (True ∨ p5)) ∧ p4) ∨ ((((True ∧ p2) ∧ False) ∧ (p3 ∨ p1)) → p5)) := by
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
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_557671060219028984084415970943 : (((p3 ∨ ((p4 → p2) → (((((p4 ∧ p5) → p2) → p4) ∨ p5) → ((p5 ∧ (((p3 ∨ p4) ∨ (p3 ∧ p1)) ∧ p4)) → (False ∨ p4))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h2
      case inl h13 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263592683939617850050344677908 : (True ∧ ((p5 → ((p1 ∨ ((p2 → (p2 ∨ p3)) → ((True → p3) ∨ False))) ∨ (((True ∧ p5) → False) → True))) ∨ (((p5 → p3) → p5) → p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_328715552301557394753169486805 : (True → ((p1 ∨ ((p3 ∨ p4) ∧ ((True ∨ False) ∧ ((p3 ∧ p4) ∧ False)))) ∨ (((p1 → True) → (p1 ∧ True)) → (p1 → ((p3 → p1) ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347655984292647860777300013050 : (p3 → (((p1 → p2) ∧ (p2 → False)) → ((((p2 → (p4 → p5)) ∧ p1) → (((p1 ∧ (False ∧ (True ∨ False))) → True) → p2)) ∨ (p4 ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h9 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h9
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259468304444292245015715466424 : ((False → p4) → ((p3 → p2) → (((p3 ∧ p3) ∨ p4) ∨ (False → ((p2 ∧ (False → p3)) ∨ (p5 ∧ (p5 ∧ ((True ∨ (p1 ∨ True)) ∨ False)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339848870669217291145353057517 : (p1 → (True → ((p3 ∨ ((p3 ∧ p4) ∨ ((True → ((((p1 ∨ p4) ∧ p5) ∨ ((p1 → p2) ∨ p5)) ∧ p1)) ∧ (False ∨ (p2 → p3))))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_131645650047015430220926463005 : (((p1 → (p4 ∧ p3)) ∨ ((p5 ∨ (p1 ∨ (p3 → (p1 ∨ (p3 → (p2 ∧ p4)))))) ∨ (p2 ∨ ((p4 ∧ p4) ∨ True)))) ∧ ((p5 → False) → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594491628622852694265120876903 : (((((((((p4 ∨ True) ∧ True) → ((p4 → False) ∨ p3)) ∨ (p5 ∧ p3)) ∧ (p5 ∧ p3)) ∨ ((((p5 → p4) ∧ False) → p5) ∨ p1)) ∧ True) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45778242751976751486868357701 : (((p1 → (((False → ((p3 → ((p2 → True) → True)) ∨ True)) ∧ ((p1 → ((p3 ∧ p2) ∧ (False ∨ (True ∧ True)))) → p4)) ∧ p3)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_143032576466159287905953271918 : ((False → (((((((p4 ∧ p5) → p2) ∨ p2) ∧ (p2 ∧ (((p2 → p3) ∨ p4) ∧ p4))) ∨ (p2 ∨ p4)) ∧ p2) ∧ p5)) → ((p2 ∧ p1) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160920872712954893107457785820 : ((((False ∨ True) ∧ (False → p2)) → (True ∨ ((p2 ∧ ((((p4 → False) ∨ True) ∧ p3) → p5)) → False))) → ((True ∨ p3) → ((False ∧ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_179417757412742857638632186457 : ((p4 ∨ ((True → ((((p2 ∧ (p1 ∨ p4)) ∨ False) ∨ p2) → p4)) → p1)) ∨ ((((p4 ∨ p5) ∨ ((False ∨ p2) → False)) → p4) ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216659211629861139755490614506 : ((((p3 ∨ p3) ∨ p1) ∧ p3) → ((True ∧ True) → ((True ∨ p4) → (p2 ∨ ((p3 ∨ ((p1 → p4) → ((p1 ∨ p5) ∧ (True → p5)))) ∨ p3))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h1.left
    let h8 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h20 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h21 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47341674806266239648394220901 : ((((p3 ∨ p3) ∧ (True → (((True ∨ True) ∧ (p2 → (p4 ∧ p4))) ∧ ((True → ((False ∨ p2) ∨ p4)) ∨ (p1 ∨ False))))) ∨ (p3 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658504924292145602962118308984 : ((((p2 ∨ ((p1 ∧ ((p3 ∧ (((p1 ∨ (p1 ∨ (p3 → True))) ∨ (p1 → p3)) ∨ ((p1 ∨ p1) ∨ p2))) ∨ p3)) ∧ False)) ∨ (True ∨ True)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_344591564614597230643758158060 : (p2 → (p1 → (((p1 → ((True ∨ (True ∨ p3)) → p3)) ∨ (p4 ∨ ((p3 → p5) ∨ ((p4 ∨ ((p3 → p5) ∨ False)) ∨ (True ∧ False))))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157520310800015692009983739866 : (((p5 ∨ (p5 ∨ ((p5 → ((((True ∨ p5) → p4) → True) → (True ∨ p4))) → p5))) ∨ (p5 ∨ p4)) ∨ ((False ∧ p2) → (True ∨ (p3 ∨ p5)))) := by
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
theorem thm_5_vars_114777808253900548958267289516 : ((((((p4 → p1) → (p4 ∧ ((p3 → (p1 ∧ p3)) ∨ True))) ∨ p2) ∨ True) ∧ (((p3 ∨ p3) → p2) ∨ (p3 → (True ∨ p4)))) ∨ (p1 ∧ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116180421618447531895765923897 : (((p3 → (p1 → p1)) ∧ ((p4 → p2) ∨ (((p3 ∧ (p5 ∧ (p3 ∨ p2))) ∨ (True ∧ (p5 ∧ ((p3 ∧ p3) ∧ True)))) ∧ p5))) ∨ (True → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172561972837876114925703866683 : (((p4 ∧ (False ∧ p2)) ∨ ((p5 → ((True ∧ ((p4 → p1) → p3)) ∨ p2)) ∧ p2)) ∨ (p1 → (p3 ∨ ((False ∧ ((True ∨ False) ∨ p2)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_171947537089960263223946323937 : ((((p1 ∨ (((p3 ∨ p2) → (p3 ∨ p3)) ∨ p2)) → (p2 ∧ p5)) ∧ (p3 ∧ True)) ∨ (((p3 → True) ∧ (p2 ∨ ((p5 ∨ False) ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_756634841279689239295132886 : ((((p2 ∧ p3) → False) → (((((((False → p1) → (p3 ∨ False)) ∨ (p5 ∨ p3)) → True) → False) ∧ (p4 ∨ (p2 ∨ p5))) → p2)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((((False → p1) → (p3 ∨ False)) ∨ (p5 ∨ p3)) → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h6
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : ((((False → p1) → (p3 ∨ False)) ∨ (p5 ∨ p3)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204295185759388286292390993794 : ((((p3 → p2) → (p1 ∨ p3)) ∧ p3) ∨ (((False ∨ (p5 ∧ (p3 ∨ (p3 ∧ p3)))) → (p1 ∨ (p2 → (p3 → (True ∨ (False ∧ p5)))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134037648293951143805350035857 : ((((((p1 ∧ (True ∨ ((p4 ∨ p3) ∨ False))) ∧ False) ∧ ((p1 ∨ (p1 ∧ (p4 → p4))) ∨ (p1 ∧ p1))) ∨ True) ∨ p3) ∨ (p3 → (p5 ∨ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184979367604618819007480839240 : (((False → (p5 ∨ False)) → ((False ∧ False) ∨ (p3 ∨ (p5 ∨ False)))) ∨ (False → (((p3 → (False → p5)) ∨ (p3 → (p1 ∧ False))) ∨ (p5 → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137290098770483688760457615399 : ((p2 ∧ ((False ∧ (p2 → (p5 ∧ (((p5 → True) ∧ (((p5 ∧ False) ∨ p4) → p4)) ∧ ((p3 → p3) → False))))) ∨ p5)) ∨ (True ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179761174764930036258425198288 : ((((((p4 ∧ True) ∨ (p5 ∧ p3)) → p1) ∨ (p1 ∧ (p4 ∨ p5))) ∧ True) → ((((p2 ∨ True) ∨ ((True ∧ False) ∨ p2)) → p2) → (p5 ∨ p2))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h6 : ((p2 ∨ True) ∨ ((True ∧ False) ∨ p2)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : ((p2 ∨ True) ∨ ((True ∧ False) ∨ p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42644938802622457724735715782 : (((p4 ∨ (((p5 ∧ ((p1 → (p5 ∨ p3)) → ((p2 ∨ True) → p1))) ∧ ((True → (p1 → False)) ∧ ((p3 ∨ p5) ∨ p4))) ∧ p4)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703479900217076165948656519103 : ((((p5 ∨ (False ∨ (True → ((True → False) ∧ (p3 → p3))))) ∨ (((((((p5 → p4) → True) ∧ p5) ∨ p1) ∨ p2) → p5) ∨ (p5 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937757382538167285253044744985 : ((((p4 ∧ ((True ∨ p5) ∧ (p5 → False))) ∧ ((((False ∨ p4) → (False ∧ ((p2 ∧ (False ∨ True)) → (p3 ∨ p4)))) ∧ (p3 → p1)) ∧ p3)) → p2) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h3.left
    let h10 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : (False ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h14 := h11 h13
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h3.left
    let h18 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h17.left
    let h20 := h17.right
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h21 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h22 := h7 h21
    -- False on the left can always be used.
    apply False.elim h22
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165020441445520848812966728814 : (((((True ∨ (p1 ∨ False)) ∨ p1) → (p1 → ((p2 ∨ (p3 ∨ p5)) ∨ (p2 → p3)))) → p4) ∨ (p5 ∨ ((False → p1) ∨ (p2 ∧ (p4 → True))))) := by
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
theorem thm_5_vars_135007643879126899542060227887 : (((False ∨ (False ∧ (p4 → (p2 ∧ ((p5 ∨ p5) ∧ ((True ∧ (p5 ∧ False)) → ((p2 ∧ p1) ∨ False))))))) ∧ (p4 ∧ p4)) ∨ (p1 → (p2 ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199522353136744432114345858186 : (((p5 → (True → ((p5 ∨ p2) ∨ p3))) ∨ p5) → ((((p3 → (p4 → (p3 ∨ p4))) ∨ ((p2 → (p3 ∧ False)) → p1)) → False) → (True → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p3 → (p4 → (p3 ∨ p4))) ∨ ((p2 → (p3 ∧ False)) → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h8 := h2 h5
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : ((p3 → (p4 → (p3 ∨ p4))) ∨ ((p2 → (p3 ∧ False)) → p1)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h11
      -- Implications on the right can always be decomposed.
      intro h12
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h11
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h13 := h2 h10
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185453835101601528067019503913 : ((False ∨ (p2 → (((p4 ∨ (p2 ∧ p4)) → (p3 ∨ False)) ∨ True))) ∨ ((p3 → (((p2 → p1) ∨ False) ∧ p5)) ∨ ((p4 → p3) → (True → p4)))) := by
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
theorem thm_5_vars_215509998011826066329871644842 : ((p4 ∧ ((p4 ∨ p3) → p3)) ∨ (p3 ∨ ((((((p3 ∨ p2) ∧ False) ∧ p5) ∧ p2) ∧ True) ∨ ((p3 ∧ (False ∧ (p3 → (False ∨ p2)))) → False)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148702651640223359960644511658 : (((((((p4 ∨ p2) ∧ p4) ∧ False) → p5) ∨ False) → ((p1 → (False ∨ True)) ∧ (p2 ∨ ((p4 → p1) ∨ p1)))) ∨ (p1 → (p5 → (False ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250826252318446350678255049408 : ((p1 → p2) ∨ (((p3 ∨ (p5 → ((True → p3) ∨ False))) → (((((p5 ∧ p1) → p5) → True) → p2) ∧ True)) ∨ (False → ((False → True) ∨ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747436911098587927358868025054 : ((((True → False) → ((p3 ∧ (False ∨ ((p1 ∨ p5) → ((p3 → (((p2 ∧ p1) ∨ ((p4 ∨ p3) ∧ p3)) ∧ False)) ∨ (p3 ∨ False))))) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353475266068892393210300819833 : (p4 → (p2 ∨ ((p5 ∨ (p3 → (False ∧ (((p5 ∧ (p1 → True)) ∧ (p5 ∨ (p5 ∨ ((False ∨ ((p2 → p3) ∨ True)) ∧ p3)))) ∧ p5)))) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780495930496280002089031676324 : (((p2 ∨ ((((p2 ∧ p4) → p2) ∧ (True ∧ (((p3 → (p2 → True)) ∨ p4) ∧ p5))) → ((p1 ∧ p3) ∨ ((p2 ∧ (p1 → p3)) → p2)))) ∨ p1) ∧ True) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_963523820724050255619080369938 : ((((p3 → False) ∧ (p3 ∧ ((((p2 → (p5 ∧ p4)) ∧ True) ∨ p4) ∧ (True ∨ (((True ∧ (p1 ∨ (p3 ∧ True))) ∨ p5) ∨ (p5 ∧ False)))))) → p4) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h11 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h12 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h13 := h2 h12
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h15
        case inl h16 =>
          -- Conjunctions on the left can always be decomposed.
          let h17 := h16.left
          let h18 := h16.right
          -- Disjunctions on the left can always be decomposed.
          cases h18
          case inl h19 =>
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h20 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h4
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h21 := h2 h20
            -- False on the left can always be used.
            apply False.elim h21
          case inr h22 =>
            -- Conjunctions on the left can always be decomposed.
            let h23 := h22.left
            let h24 := h22.right
            -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
            have h25 : p3 := by
              -- One of the premise coincides with the conclusion.
              exact h23
            -- We have shown the premise of h2, we can now drive its conclusion.
            let h26 := h2 h25
            -- False on the left can always be used.
            apply False.elim h26
        case inr h27 =>
          -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
          have h28 : p3 := by
            -- One of the premise coincides with the conclusion.
            exact h4
          -- We have shown the premise of h2, we can now drive its conclusion.
          let h29 := h2 h28
          -- False on the left can always be used.
          apply False.elim h29
      case inr h30 =>
        -- Conjunctions on the left can always be decomposed.
        let h31 := h30.left
        let h32 := h30.right
        -- False on the left can always be used.
        apply False.elim h32
  case inr h33 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h34 =>
      -- One of the premise coincides with the conclusion.
      exact h33
    case inr h35 =>
      -- Disjunctions on the left can always be decomposed.
      cases h35
      case inl h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Conjunctions on the left can always be decomposed.
          let h38 := h37.left
          let h39 := h37.right
          -- Disjunctions on the left can always be decomposed.
          cases h39
          case inl h40 =>
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- One of the premise coincides with the conclusion.
            exact h33
        case inr h44 =>
          -- One of the premise coincides with the conclusion.
          exact h33
      case inr h45 =>
        -- Conjunctions on the left can always be decomposed.
        let h46 := h45.left
        let h47 := h45.right
        -- False on the left can always be used.
        apply False.elim h47
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51933691112086977376435448684 : ((((p5 ∨ (p5 ∨ (True → ((p5 → (p1 → p2)) ∨ p2)))) → (p5 ∧ (False ∨ p3))) ∨ (p4 → (((p5 → p4) ∧ p1) ∨ (p3 ∨ True)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_171687609641363369231886661201 : (((p4 ∨ (p3 ∧ ((True → ((False ∧ False) ∧ p1)) ∧ ((False ∨ p4) ∧ p2)))) ∨ p5) ∨ (((True ∧ (((p2 → p5) → p5) ∨ True)) ∨ False) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178418350664487638197811079043 : (((p2 ∨ (p3 → ((False ∨ (p5 ∧ (p4 → True))) ∨ True))) → (p4 ∧ p1)) ∨ (True ∨ ((True → p5) → ((True ∨ (p4 ∧ (p5 ∨ p5))) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115760330373466385128270653109 : (((False ∨ (p3 ∧ ((True → p5) → p1))) → ((p4 ∨ ((((((p3 → (p5 ∨ p5)) → p1) ∨ p5) ∨ p1) → True) → p5)) → False)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98827908522190716034227258646 : ((True → ((p4 ∨ (p1 ∨ (((((p4 → True) → ((False → (p4 → p5)) → p4)) ∨ (p3 ∨ ((p2 → p1) ∧ p5))) → p2) → True))) ∧ False)) → False) := by
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
theorem thm_5_vars_49570982453435065648964256668 : (((((p4 ∨ ((((False → True) ∧ False) ∧ False) ∧ False)) → (True → (True ∨ p1))) ∧ ((p4 ∨ (False ∧ p2)) ∧ p3)) → (p5 → (True ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156892759019342738811456934450 : ((((((p1 ∨ True) → p2) ∧ (p4 → ((p3 → False) ∧ ((False ∧ (p1 ∨ p3)) ∧ False)))) ∨ p5) ∨ True) ∨ ((p1 ∨ ((p5 → p4) ∧ False)) ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171438569868858870369585281057 : ((((p3 → p3) → ((((p3 ∨ p4) ∧ (p2 ∨ p3)) → (p2 ∨ p5)) → p4)) ∧ p4) ∨ (p1 ∨ ((True → ((p4 ∧ (p2 ∧ p3)) ∧ p5)) → p2))) := by
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
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219332402315025111690118589450 : ((p2 ∨ (p1 ∨ (p5 → True))) → (p2 → ((((p2 → True) ∧ ((p1 → (p5 ∨ (((p2 ∧ p5) → p1) → True))) → p5)) ∨ p3) ∨ (p4 → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138635232320735741024815513475 : ((((p5 ∧ (((False ∧ (p5 ∧ (p3 → (p5 → p5)))) ∨ (p4 ∨ (True ∧ p2))) ∨ (p2 ∧ p5))) → (True ∨ p2)) ∧ True) → ((p4 → p2) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604287760749030592637529853034 : ((((True → (((p3 ∨ (p5 ∨ (False ∧ p3))) ∨ (p3 ∨ ((p5 ∨ ((True ∧ (p2 → p2)) → p5)) ∧ p1))) ∧ ((p3 ∧ p5) ∨ False))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_604834879512888222239214077233 : ((((p1 → ((p3 ∧ ((p1 ∨ ((p3 → p2) → p4)) ∨ (((((p4 ∨ p3) ∨ p1) ∧ p3) ∧ (p4 ∨ p3)) ∨ p3))) → (False ∧ False))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668691912205589514222338482173 : (((((((((p1 → ((True ∧ p2) ∨ p3)) ∧ (p4 → p1)) ∨ (True ∧ p1)) → (p3 ∧ (p5 → p5))) ∧ p5) ∨ False) ∨ ((p5 ∧ p2) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731506213300293443616214643410 : ((((False → (False ∧ False)) → ((((((p5 → (True ∨ p2)) → p5) ∧ p3) ∧ False) ∧ (((True ∨ (False ∧ p1)) ∧ p3) ∨ (p3 ∧ True))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195525244127208318914366601945 : ((((p5 ∨ False) ∨ p3) → ((p2 → True) ∨ False)) ∧ (((p5 → p2) ∨ (((((p5 → True) → p5) ∨ p5) ∧ (p5 ∨ (p4 → p3))) ∧ p2)) ∨ True)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659562105059114954436932968181 : ((((((((p3 ∧ ((p3 ∨ p4) → ((((p1 ∧ p3) ∧ p4) ∨ p5) ∧ p5))) ∧ p3) ∨ True) → ((False → False) ∧ p3)) ∧ True) → (p1 ∨ p3)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ ((p3 ∨ p4) → ((((p1 ∧ p3) ∧ p4) ∨ p5) ∧ p5))) ∧ p3) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218421375236036865202157983756 : (((p1 ∧ p4) → (True ∨ True)) → ((((((p2 ∧ p2) → (p2 → p1)) ∧ (((False ∨ (p2 ∧ p2)) ∧ p3) ∧ p3)) ∧ True) ∨ p5) ∨ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118672868977448308148343625359 : ((p4 ∨ (p2 → (((p1 → p4) → (((True → (p5 → False)) ∧ p5) ∧ (p2 ∧ p3))) → ((False ∨ ((False ∨ p2) ∧ p4)) → False)))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160290430459215722532027591437 : (((((p1 ∧ (p5 ∨ ((True ∨ ((p5 ∧ p3) ∨ p2)) → (p5 ∨ p1)))) ∧ p2) → p4) → (p5 ∧ False)) → ((((p4 ∨ p4) → p5) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42686313242784142495863811865 : (((p5 ∨ (((((p2 ∨ (((p1 ∨ (p1 ∧ p5)) ∨ p4) ∨ p3)) ∨ (((False ∧ p5) ∨ p4) → p1)) ∧ (p4 ∨ p1)) ∧ p3) ∨ True)) ∨ p3) ∨ p2) := by
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
theorem thm_5_vars_48656651833025604897578667044 : (((((True ∧ p4) ∧ (p5 → (p3 ∨ (((p5 ∨ p2) → p3) → (True ∨ True))))) → (((True → p1) → p3) ∧ True)) ∧ (p1 ∨ (p4 → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769534671955563002319172876331 : (((p5 ∧ (p4 ∧ ((p1 → ((((p5 → p1) ∧ (((p1 → (((p1 ∨ p2) → p4) → (True ∧ p4))) ∨ p5) → True)) ∨ p1) ∧ p4)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157933669279780837713320945627 : ((((True ∧ (p3 ∧ (True ∧ p5))) ∧ (p3 → p4)) ∧ (p1 ∨ ((p4 ∨ p5) → (True → (True ∧ p5))))) ∨ ((p2 ∨ ((True ∨ p5) ∨ p3)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118723511224376444859960276823 : ((p5 ∨ ((((p4 ∨ ((p5 → p2) ∨ p1)) → p5) ∧ (p3 → ((p5 ∨ (p4 → (p1 ∨ False))) ∧ False))) ∨ ((False ∨ False) → p4))) ∨ (p3 ∧ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_47071803464309111833439728062 : ((((p2 ∨ (p3 ∧ (((p1 ∨ (p3 ∧ True)) ∧ ((p3 ∨ p2) ∨ True)) ∨ ((p2 ∨ (p1 → p5)) ∨ p1)))) ∨ (p1 → p5)) ∨ (p3 → True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158800862058643058634246491688 : ((p5 ∧ (((p2 ∧ True) ∨ True) → ((p3 ∨ (((p5 → (p5 ∨ True)) ∨ p1) ∨ False)) → (p1 ∧ p2)))) ∨ ((((p4 ∨ p2) ∨ p5) → p1) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



