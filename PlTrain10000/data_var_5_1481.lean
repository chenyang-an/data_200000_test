variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616043796274369419140388194340 : (((((True ∧ ((p3 → (False ∨ p1)) ∨ ((((p4 → True) ∧ True) → p5) → p5))) → ((((p5 → p1) → (p5 ∨ p2)) ∨ p2) ∨ True)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_167278578230788191711031501483 : (((((p3 → (((True ∧ (False ∨ (p4 ∧ (p1 → p5)))) → p5) → p1)) → True) ∨ p1) → False) → ((((p5 ∨ p4) ∧ (p2 ∨ p2)) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 → (((True ∧ (False ∨ (p4 ∧ (p1 → p5)))) → p5) → p1)) → True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_782918546901628175978689532027 : (((p3 ∨ ((((p4 ∧ ((True ∨ (True → (p5 → p4))) ∨ (p2 → p1))) → False) ∨ (p3 → ((p3 ∨ (p2 ∧ p2)) ∨ False))) ∧ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66123659379872839299513957579 : ((p5 ∨ ((p4 → ((((p5 → (p2 ∧ ((p5 → p3) ∧ p3))) ∧ (p3 ∨ p2)) ∧ p4) ∧ ((p4 ∧ (p3 → (p1 → p3))) ∧ False))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87290630866458887947062900813 : ((((p3 ∧ (p5 ∨ (p1 ∧ p4))) → p2) ∧ (((p3 ∧ False) → ((p1 → (p5 ∨ False)) ∨ (p4 ∧ p2))) → ((p3 ∧ (True ∧ p5)) ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ False) → ((p1 → (p5 ∨ False)) ∨ (p4 ∧ p2))) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344834997634115577931485859911 : (p2 → (p5 → (((p2 ∧ True) ∧ (((True ∨ ((p4 ∧ p5) ∧ (p1 → ((True ∧ (p5 ∧ p3)) ∧ (False → False))))) → p1) ∨ (p1 → p3))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2175581053833838059966734170 : (((((p5 ∧ (((False ∨ p4) → p5) ∨ p2)) ∨ p5) ∨ (p2 ∨ (False ∨ False))) ∧ True) ∨ ((((True ∧ True) → (p4 ∨ p5)) ∧ True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61570765780130215068038349470 : ((p1 ∧ (((p4 ∨ False) → (p1 ∧ (p2 ∧ p5))) → ((p2 ∨ (p4 ∧ p5)) → ((p4 ∧ p2) ∨ (p5 ∧ (True ∨ ((p4 ∨ False) ∨ p5))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_763408247817665956428629763280 : (((p3 ∧ (True ∧ (False ∨ (((False ∨ (p1 ∧ False)) → (False ∨ ((True ∨ p1) ∧ ((p5 → (p2 → (p5 → p3))) ∧ (p2 ∧ p4))))) → p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159499200738269837437752589530 : (((((p3 → True) ∨ False) → (((False ∨ False) ∧ False) ∧ ((((p2 → p2) → p4) ∧ p1) → p2))) ∧ p4) → (((True ∨ (p2 ∧ p5)) → p3) ∧ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h1.left
    let h5 := h1.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : ((p3 → True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h16 : ((p3 → True) ∨ False) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h17
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h18 := h14 h16
    -- We need to get the left conjuct of h18 based on <expert-advice>.
    let h19 := h18.left
    -- We need to get the right conjuct of h19 based on <expert-advice>.
    let h20 := h19.right
    -- False on the left can always be used.
    apply False.elim h20
  -- Conjunctions on the left can always be decomposed.
  let h21 := h1.left
  let h22 := h1.right
  -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
  have h23 : ((p3 → True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h24
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h21, we can now drive its conclusion.
  let h25 := h21 h23
  -- We need to get the left conjuct of h25 based on <expert-advice>.
  let h26 := h25.left
  -- We need to get the right conjuct of h26 based on <expert-advice>.
  let h27 := h26.right
  -- False on the left can always be used.
  apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259880891715999591097830600128 : ((p1 → p4) → ((p2 ∨ ((False ∨ (p4 ∨ (True → p2))) → (p4 ∧ False))) ∨ (True ∨ ((p3 ∨ True) → (False → ((p1 ∨ p3) → (False → p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178187545173448928085065541104 : (((p2 ∧ (p4 ∨ (p5 → (((False ∧ p5) ∧ False) → (p4 ∧ p3))))) → p5) ∨ (((p1 ∨ (p4 ∧ True)) → (p3 ∧ (p2 → True))) ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157966657405734090881690878533 : ((((p4 ∧ p2) ∧ (p5 ∨ ((p2 ∨ p5) ∧ p2))) ∨ ((p2 ∨ p4) ∧ (True ∨ (p3 → (True ∧ p3))))) ∨ ((p4 ∧ p4) ∨ (p1 → (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256109634852961345578725147493 : ((True ∨ p5) → ((((p1 ∧ ((((p1 → p5) → False) ∧ p5) ∧ (p1 ∧ False))) ∧ p4) ∧ ((p3 ∧ p3) ∧ p3)) ∨ (((p1 ∨ p2) ∧ False) → p3))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- False on the left can always be used.
      apply False.elim h5
    case inr h7 =>
      -- False on the left can always be used.
      apply False.elim h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199983687336977150654657093858 : ((((p5 → (p4 ∧ p4)) ∧ p4) → (p1 → p1)) → (p3 ∨ ((p2 ∧ (p5 ∧ False)) ∨ (p4 ∨ ((p3 ∧ p1) → ((p2 ∧ (True → p4)) → p2)))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h2.left
  let h7 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49312856565728438736872557723 : (((p2 ∨ ((((((p2 ∨ p3) ∧ p2) → p3) ∧ (True → (p4 ∧ p3))) ∨ p2) ∧ (((p2 ∧ True) ∨ p3) → p2))) ∨ (False → (p5 ∧ p3))) ∨ p4) := by
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
theorem thm_5_vars_114299146869982625024682826394 : (((((True ∧ (((((p4 ∧ p3) ∨ p4) → p4) ∨ p5) → False)) ∧ p1) ∨ (p1 ∧ (p4 ∧ p4))) ∧ (p2 ∨ ((p4 ∧ False) → p2))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138061893432920614250799722520 : ((True → (False ∨ (p2 ∧ (((p1 ∧ p4) ∧ ((p2 → ((p1 ∨ ((p5 ∧ p3) ∧ (p1 ∨ True))) ∨ p5)) ∧ p3)) ∨ p3)))) ∨ (p3 ∨ (p5 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734873917909399367799511039998 : ((((p2 ∨ p2) ∧ (p5 ∨ (p3 → (((((p1 ∨ ((p2 ∨ (p4 ∧ (p5 → p1))) → (p5 ∨ p2))) ∨ False) ∧ (p4 ∧ p4)) → p1) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117281188545551928228150483844 : ((False ∧ ((p4 ∧ (p5 ∧ ((((p1 ∨ (False ∧ (p3 ∧ ((p1 ∧ p2) ∧ p3)))) ∧ p2) ∧ (p1 ∧ p5)) ∧ (False → p5)))) ∨ p2)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114126232807542785117744093807 : (((p2 → (p4 → (((((True → (p1 → p3)) ∧ False) ∧ ((p5 ∨ (p5 ∧ p5)) ∨ True)) ∧ p4) ∧ p5))) ∨ (False ∨ (True ∨ p1))) ∨ (True ∧ False)) := by
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
theorem thm_5_vars_123110709534888871437072798422 : ((((True ∧ (p1 ∧ ((((False → ((False ∨ p5) ∨ True)) → p1) → p2) ∨ p3))) ∨ (p1 ∨ (p1 ∨ True))) → ((p2 → True) ∧ False)) → (p2 ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ (p1 ∧ ((((False → ((False ∨ p5) ∨ True)) → p1) → p2) ∨ p3))) ∨ (p1 ∨ (p1 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342008943786569975183272841683 : (p2 → ((p1 ∧ ((p4 → p2) ∧ ((p4 → p1) → ((True → p1) ∨ (p1 ∨ ((p3 ∨ ((p1 ∨ p2) ∨ True)) ∧ p5)))))) ∨ (False → (p4 ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748759880069258861226583664924 : ((((p3 → p5) → ((p4 ∨ p5) ∨ (((p3 ∨ p2) → (p2 → ((p2 → p4) ∨ (p3 ∨ True)))) ∧ ((((p1 ∨ True) ∨ p4) ∧ p3) → True)))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205173853382888412522505223588 : (((False ∨ (p4 ∧ p3)) ∧ (p2 ∧ p3)) ∨ ((p4 ∨ p4) → (p5 → ((p3 ∧ ((((((p3 ∧ p3) ∧ p2) ∧ p1) → p2) → p4) → p3)) → p5)))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228464885175209713456652984079 : ((False ∨ (p4 ∨ p1)) ∨ (False ∨ ((((p1 ∧ p4) ∨ p5) → (p2 ∧ ((p3 → p3) → ((p3 → p1) ∧ (p2 ∨ ((p3 → p2) ∨ p1)))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65340532345271229244685552065 : ((p3 ∨ (((((p1 ∧ ((p2 → (p5 ∨ False)) ∧ p5)) → (False ∧ p1)) ∧ True) ∨ (True ∨ p2)) ∧ (p1 ∨ (p3 ∨ (p4 ∨ (p5 ∧ True)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112901704756901118681699097007 : ((((False ∧ True) ∨ (((((True ∨ p4) ∨ p3) → p1) ∧ p2) ∨ ((p5 ∨ (((p2 → False) ∧ True) ∨ (p2 ∧ True))) → p4))) → p5) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137258239257197164356517401416 : ((p1 ∧ ((True → p2) ∨ (p2 ∨ (p2 ∧ ((p2 ∧ (True ∨ ((p5 ∨ False) ∨ ((p4 ∧ False) → (False → p3))))) → p5))))) ∨ ((p1 ∧ True) → p1)) := by
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
theorem thm_5_vars_41916685777352963889729375581 : (((((p3 → p1) → p5) → ((((((False ∨ p4) → True) → p2) ∧ p1) ∨ (((p4 ∧ p5) ∨ ((False ∧ p1) → p3)) → p4)) ∨ p3)) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780030498141664053228961304981 : (((p2 ∨ ((((p1 ∨ p1) ∨ p5) ∧ ((True ∧ (((p4 ∧ p2) ∨ (True ∧ p3)) → True)) ∧ (((p4 ∧ True) ∨ p3) ∧ p2))) ∨ (True ∨ p2))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113692926620936533729891892155 : (((((p3 → ((p2 ∨ ((p2 → p2) ∧ True)) → p1)) ∧ (p5 ∨ (p2 ∨ ((p5 → p5) → (p3 ∧ p4))))) → p2) → (p2 → p3)) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_431831902193498477194659075969 : ((((False ∨ (((((((p5 ∨ p4) ∨ p3) ∨ ((p3 ∨ p4) ∧ ((p2 ∧ (p5 → False)) → p2))) ∨ p2) ∨ p1) → p1) → False)) ∨ (p5 → True)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_627095576122399487069575118097 : ((((((False ∨ ((False ∨ True) ∧ (((p3 ∨ True) ∧ (((True → ((p1 ∧ p1) → p4)) ∨ True) ∧ p2)) ∧ (p1 ∨ p5)))) ∧ p1) ∧ p4) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_555904481771886333740266955265 : (((p3 ∨ ((((False ∧ p3) ∧ (p2 → ((p5 ∨ (p1 ∧ (p1 → (p5 ∨ (p3 → p5))))) ∧ (p3 ∨ False)))) ∧ (p2 → (p2 → True))) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_260584655652384137723806535525 : ((p3 → p2) → (((((False ∨ ((p4 → (False ∨ (True → ((False ∧ p4) ∨ False)))) ∨ ((p5 ∨ True) ∧ (True ∨ p2)))) → p5) ∧ p2) ∨ p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168682149671686092435500340326 : ((p5 ∧ (((p1 ∨ True) ∨ False) ∨ ((True ∧ (p5 → ((p3 ∧ (p2 ∧ p4)) ∨ p3))) → p4))) → (((p1 → p4) ∨ (False ∧ True)) ∨ (p5 ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_893295934196695626093920307549 : (((((((True ∨ (p4 → p3)) ∨ p4) → (False ∧ p2)) ∧ ((p3 ∧ (p4 ∨ True)) → (p5 ∨ (p1 ∧ (False ∧ p1))))) ∧ (p1 → (p3 → p5))) → p4) ∧ True) := by
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
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : ((True ∨ (p4 → p3)) ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h7 := h4 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108275063922752176392809292844 : ((True ∧ (((p4 ∧ (p2 ∨ (True → False))) ∨ (p5 ∧ (True → p2))) ∨ (((True → (((False ∧ p5) → True) ∨ p5)) ∧ p3) ∨ True))) ∧ (True ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_832432907568037020293066294017 : ((((p5 → (((((True → (True ∧ (p2 ∨ p2))) ∨ p4) ∧ (p4 ∨ True)) ∨ (((True ∧ p1) → (False ∧ p3)) ∨ (p3 → p5))) → False)) ∧ p5) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((((True → (True ∧ (p2 ∨ p2))) ∨ p4) ∧ (p4 ∨ True)) ∨ (((True ∧ p1) → (False ∧ p3)) ∨ (p3 → p5))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684179015646525045026699376911 : (((((False ∨ ((((p5 ∨ (False ∨ ((p3 ∧ False) ∨ False))) ∧ p5) ∧ p2) ∧ p5)) ∨ (False ∨ p4)) ∨ (p1 ∧ (p1 ∨ (p4 ∧ (p2 ∨ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342887620569503660933726435726 : (p2 → ((((False ∨ p1) ∨ (p1 ∨ p3)) ∨ p5) → (True ∧ ((p3 ∨ ((p4 ∧ (p3 ∧ p4)) ∧ p3)) ∨ (((p4 ∧ True) ∧ (p3 ∧ p5)) → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h10
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764717059201732940302405888069 : (((p4 ∧ ((p3 ∨ ((((p3 ∨ True) ∧ p5) ∨ ((p1 ∨ (p1 ∧ p1)) ∧ (((p1 ∨ True) ∨ ((True → p5) ∨ False)) → p4))) ∨ False)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190777750533367026463776712860 : ((((False ∧ (p2 ∨ (p4 → p4))) ∨ p4) ∨ (p1 ∨ p4)) ∨ (((p1 ∨ (p5 ∧ (False → ((p5 ∨ (True ∨ p5)) ∨ True)))) ∧ (True ∧ p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44407572064714213284161306606 : ((((((((p4 → p4) → True) ∧ (p4 → (p3 ∧ False))) → p5) ∨ (False → False)) → (p2 → ((((False ∨ p3) → True) → True) → p2))) → False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_628299629464217400221342841709 : ((((((p5 ∧ p4) → (((p5 → (p3 → p2)) ∨ ((p3 → p3) ∨ (((True → p2) → (False → p5)) → (p3 → p5)))) ∨ p4)) ∧ p2) → p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121357606381809232657146454843 : ((((((((p3 → p3) ∧ p1) ∧ p3) → ((((True → ((p3 → (p4 ∧ p1)) ∨ p2)) ∨ False) ∧ False) ∨ p2)) ∧ False) ∨ p2) → p2) → (p4 → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165998074056984602845707914606 : (((p4 ∧ p3) ∨ (p2 ∧ (((p1 ∧ p4) ∨ (True ∧ (p2 ∨ False))) ∨ (p2 ∧ (p2 ∧ p2))))) ∨ ((False ∧ ((True ∨ True) ∨ (False → True))) → False)) := by
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
theorem thm_5_vars_115554492815817726348113341444 : ((((True ∧ (p2 ∧ (p5 ∨ False))) ∧ p4) ∧ (((p1 → (((((p5 → (p4 ∧ p3)) → False) → p5) → p5) → True)) → p5) → False)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_662764007983400209637151677241 : ((((((True → p4) ∨ (p2 ∧ p2)) → ((False ∧ (p2 → (p2 ∧ ((True ∨ (False ∧ p4)) → True)))) ∨ (True ∨ (True ∨ p4)))) → (False ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134381477272579221682214364098 : (((p4 ∨ ((((p5 ∧ (False → ((p1 → p2) → (p1 → p5)))) ∨ ((p5 ∨ p2) ∧ p5)) ∧ p4) ∧ (False → True))) ∨ p5) ∨ ((True ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172426192082300063300005172720 : (((False ∧ (True → (p1 ∨ False))) ∧ (p3 ∧ ((p3 ∨ p5) ∨ (p2 ∨ (False → True))))) ∨ ((True ∨ p1) ∧ (((p1 ∧ p3) → True) ∨ (True ∨ p5)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219731864333933042813557401590 : ((p1 → (p3 ∨ (True → True))) → ((p2 ∨ (True → ((p4 → p5) ∧ p4))) ∨ (((p1 ∧ (p1 ∧ p2)) → True) ∨ ((p2 ∨ (p4 → True)) ∨ p2)))) := by
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
theorem thm_5_vars_248700732354520808251023557800 : ((p3 ∨ p2) ∨ (((((p2 ∨ p5) ∧ p4) ∨ p3) → ((p2 ∧ False) ∨ (True → (True → ((p3 ∧ p2) ∧ False))))) ∨ (((p5 ∨ False) ∧ p3) → p5))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151145176652335619044403218534 : ((((p4 ∧ ((p5 → ((p5 → (p3 ∧ (False ∧ (p5 ∧ p3)))) → p1)) ∧ (p1 ∧ p1))) → (p1 → p3)) → False) → (p1 ∨ ((p2 → True) ∨ False))) := by
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
theorem thm_5_vars_113576866587725273381670535473 : (((False ∧ (((((p2 ∨ p2) ∧ (True ∨ ((False ∨ (p4 ∨ (True ∧ (True ∧ p1)))) ∨ p3))) ∧ True) ∨ p1) → False)) ∨ (p5 ∧ p5)) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_719513559572967763084434740066 : ((((p2 ∨ (p1 → (False ∧ p4))) ∨ (p3 → (((p2 → (((False → True) ∧ False) ∨ p1)) ∨ p5) ∧ ((p3 ∨ False) ∨ ((p4 → p5) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157643984295587671741021095939 : (((True → ((p2 → (p5 ∧ (p5 ∧ (p4 → p3)))) → ((p2 ∨ p1) → p5))) ∧ (p2 → (p3 ∨ p1))) ∨ (p1 → ((False ∨ (p2 ∨ p1)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134621379293246979778591054328 : (((((p5 ∨ (((False ∧ (True ∧ (p5 ∨ p5))) ∧ p1) ∧ True)) ∨ ((p3 ∧ p1) → True)) → ((p5 ∨ p1) ∨ p3)) → p2) ∨ (False → (p4 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304428975463896938914325688497 : (p1 ∨ (((True ∨ True) → (((p1 → (p1 ∧ p3)) → (((p4 ∨ p2) → p2) ∧ ((p2 ∧ p1) ∨ p2))) ∧ ((p1 ∧ False) ∧ (p2 ∧ p5)))) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ True) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_992171818654126422811193577946 : (((p4 ∧ ((p1 ∧ (p4 → (False ∧ (((True ∨ p4) ∧ (p2 ∨ p1)) ∨ p2)))) ∧ (((p4 → (p4 ∨ p1)) ∧ False) → (p3 ∨ (False ∧ p3))))) → False) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70049400789553027323818237063 : (((((True → (True → (False ∧ ((True → False) → (p5 ∨ (((True ∨ p2) ∨ p4) → (p3 ∧ (p3 ∧ False)))))))) ∨ (p5 → True)) → False) ∧ p4) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((True → (True → (False ∧ ((True → False) → (p5 ∨ (((True ∨ p2) ∨ p4) → (p3 ∧ (p3 ∧ False)))))))) ∨ (p5 → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748666769909802258371679637528 : ((((p3 → p3) → (((p5 ∨ ((p5 → (p2 ∨ True)) → (p3 ∧ ((False ∨ False) ∨ p2)))) ∨ ((p4 ∨ (p3 ∨ p4)) ∨ True)) ∨ (False ∧ p3))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707480003435998733200438818941 : ((((((p1 ∧ True) ∨ p1) ∨ (p4 → (p4 → p3))) ∨ (((p3 → (p2 ∧ ((True → (p1 → p3)) ∧ True))) → ((False ∧ p3) ∧ p2)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137677457409206581865241406546 : ((p1 ∨ ((((False ∧ ((False ∧ (p2 ∨ ((p5 → p4) ∨ (p3 ∨ p3)))) ∧ p2)) → (p5 → (p1 ∨ p3))) → p5) ∧ p5)) ∨ ((p5 ∧ False) → p4)) := by
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
theorem thm_5_vars_775649518975463140372460565805 : (((False ∨ (p1 ∨ ((p1 ∧ (p2 ∨ (p1 → (p5 ∧ ((p2 ∧ ((p3 → p5) → True)) → (p2 → p3)))))) ∨ (p3 ∨ ((p1 ∨ True) → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258046743062242583056187346624 : ((p4 ∨ p2) → (((((p1 ∧ False) ∧ ((p5 ∨ (p5 ∨ p2)) → (True ∨ ((p3 ∧ (True ∨ False)) ∧ True)))) ∨ p4) ∧ (True ∧ p1)) ∨ (True ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45674899703429620174234994569 : (((p5 ∨ (((p5 ∨ (p5 ∧ p5)) → (p3 ∧ (p4 → ((p3 ∧ (p4 ∧ (False ∨ True))) ∧ False)))) ∨ (p4 ∧ (p3 ∨ (p3 → p3))))) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158596614824885639413672250684 : ((False ∧ ((((p1 → (p3 ∨ p3)) ∨ p4) ∧ (((p3 → p4) → p4) ∧ ((p2 → p3) ∨ p3))) ∨ True)) ∨ ((p5 ∧ ((p4 ∧ p1) ∧ p2)) → p2)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205174328535639846662135060734 : (((False ∨ (False ∨ p4)) ∧ (p4 ∨ p3)) ∨ ((True ∨ (False ∧ (((p3 ∨ (((p4 ∧ p1) ∧ p1) ∨ True)) ∨ p5) ∨ (p4 ∧ (False → False))))) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116525489590058757702954805156 : (((p5 ∧ p5) ∧ ((p1 ∧ (p2 → p4)) ∧ ((p3 ∨ (p5 ∧ ((p2 ∧ p4) → p1))) ∧ (False ∧ (p5 ∨ ((p1 → p2) ∧ p3)))))) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119213593071801798187719329591 : ((p2 → (((True → (p4 ∨ True)) ∨ ((p3 → True) ∨ p3)) → (((p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) → False) → (p4 ∧ p4)))) ∨ (p5 ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h9 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h10 := h3 h9
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- False on the left can always be used.
      apply False.elim h13
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h14 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h15 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h16 := h3 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : (p2 ∨ (p1 ∨ ((p3 → p5) ∧ p4))) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- False on the left can always be used.
      apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160762134896903729583878756235 : (((((p5 → p1) ∨ (True ∨ p1)) → False) ∧ ((p2 ∨ (False → (True ∨ (p1 ∨ p3)))) ∨ (p4 ∨ p4))) → (p4 → (False ∧ ((False ∧ p1) ∧ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h7 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h7
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h10 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h11 := h3 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h14 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h15 := h3 h14
      -- False on the left can always be used.
      apply False.elim h15
    case inr h16 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h17 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h18 := h3 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h20
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h22 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h23 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h24 := h19 h23
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h26 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h27 := h19 h26
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h29 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h30 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h31 := h19 h30
      -- False on the left can always be used.
      apply False.elim h31
    case inr h32 =>
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h33 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h34 := h19 h33
      -- False on the left can always be used.
      apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h36
  case inl h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h37
    case inl h38 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h39 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h40 := h35 h39
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h42 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h43 := h35 h42
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h46 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h47 := h35 h46
      -- False on the left can always be used.
      apply False.elim h47
    case inr h48 =>
      -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
      have h49 : ((p5 → p1) ∨ (True ∨ p1)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h35, we can now drive its conclusion.
      let h50 := h35 h49
      -- False on the left can always be used.
      apply False.elim h50
  -- Conjunctions on the left can always be decomposed.
  let h51 := h1.left
  let h52 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h52
  case inl h53 =>
    -- Disjunctions on the left can always be decomposed.
    cases h53
    case inl h54 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h55 =>
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h56 =>
    -- Disjunctions on the left can always be decomposed.
    cases h56
    case inl h57 =>
      -- One of the premise coincides with the conclusion.
      exact h57
    case inr h58 =>
      -- One of the premise coincides with the conclusion.
      exact h58



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680649987013591240324990214225 : ((((((False ∧ p1) ∨ ((True ∧ p3) ∧ p2)) ∨ (((p2 → (p3 ∧ p3)) ∧ True) ∨ ((True ∨ p4) → p1))) → ((p5 ∧ p4) → (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56219112361232996721803036815 : (((p2 ∨ (True ∧ (False ∨ p1))) ∨ ((p5 → (p2 → ((True ∨ p2) → p4))) → (p5 ∨ (False ∨ (p4 ∧ (((p5 ∨ p3) → p2) → False)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58892368363705525871840356543 : (((False ∧ p3) ∨ ((p1 → p4) ∧ ((p3 ∧ ((p5 ∨ ((False ∨ True) ∨ p3)) ∧ p5)) ∨ (p4 → ((p1 ∨ (p3 → (True ∧ True))) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112424247951048987155364586823 : ((((p4 → ((((p2 ∧ (((p2 ∧ False) ∨ (p2 ∧ p1)) ∨ True)) → (p2 → (p1 → p5))) ∨ (p1 ∨ p4)) ∨ False)) ∧ p5) → p3) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337775808835839830360526986165 : (p1 → (((p1 → p2) → (p5 ∨ ((p4 ∨ (((False → (False ∧ False)) ∨ p3) → p3)) ∨ p2))) ∨ (((p5 ∧ p2) ∨ p3) ∨ (p4 ∧ (p5 ∧ p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114530572537468322328724744358 : (((p3 ∨ ((((p4 ∨ p3) ∧ p2) ∧ p3) ∨ ((p5 ∨ (True ∨ p2)) → (p3 → (False ∧ p1))))) → (((p3 ∨ p1) ∧ p1) → p2)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113511724770622239069553284071 : ((((p5 ∧ (p3 ∧ ((p1 → p2) ∨ (((False ∧ True) ∧ p2) ∨ p5)))) ∧ ((p3 ∧ ((p1 ∧ p1) ∨ p2)) → True)) ∨ (False ∨ True)) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111088861326860739563552308795 : ((((((False ∨ (p4 → p4)) ∨ (p2 → False)) ∧ ((p4 ∧ p3) ∧ p2)) ∨ (p2 → (((True → (p1 ∧ p2)) ∧ p4) → p5))) ∧ p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263077371493613177764188350164 : (True ∧ (((((p3 ∧ ((p4 → p2) ∧ (p2 ∨ ((p2 → (((False ∨ False) ∧ p5) → (p1 → True))) → p5)))) → False) ∨ p3) ∨ False) ∨ (True ∨ p4))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_464237879815675586451373871713 : ((((((((p2 ∧ ((p4 → (False ∨ p5)) ∨ p1)) ∧ False) ∨ False) → (False → p4)) → p2) → ((((True → p5) ∨ (False ∧ p4)) ∨ p5) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_165464418128084645720537021957 : (((True ∧ (False → (p1 ∧ ((p5 → p5) ∨ (p3 → p1))))) ∧ ((p2 ∨ p5) → (p2 ∧ p2))) ∨ ((((p5 → p2) ∧ p4) ∧ (p2 ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153530539767116154379695654487 : ((True → ((p5 → (((p3 → True) → (p1 ∧ (((p4 → (p2 ∨ p1)) → p3) → (p2 ∧ True)))) ∨ p5)) → p3)) → ((p3 ∨ (False ∧ False)) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → (((p3 → True) → (p1 ∧ (((p4 → (p2 ∨ p1)) → p3) → (p2 ∧ True)))) ∨ p5)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_713298005917111978631436118293 : ((((p5 ∨ ((p3 ∧ (p2 → p3)) ∧ p3)) ∨ (((p2 ∨ p5) → (((p3 ∨ (p2 ∧ p2)) ∧ (True ∨ True)) → ((p4 → p3) ∧ p4))) ∨ True)) ∨ False) ∧ True) := by
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
theorem thm_5_vars_149296783036299931594218155324 : (((p5 → p4) ∨ ((p2 → ((p2 ∨ (p5 → p3)) → (p4 ∧ (((p3 ∨ (p3 ∧ False)) → p5) ∧ p2)))) ∧ p5)) ∨ (((p2 ∧ True) ∧ p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780879790086226546104745356658 : (((p2 ∨ (((p5 ∨ p2) ∨ p3) ∧ (True → (p1 ∧ (p5 ∧ ((False ∧ p4) → (p3 ∨ (((p4 → (True ∧ p3)) ∨ p1) ∧ (p4 ∨ True))))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116706770536376096477715941865 : (((p1 ∧ p1) ∨ (False ∧ (((p5 ∨ (((p2 ∨ (True ∧ p4)) → p4) → (p1 → (p5 ∨ p4)))) ∧ p3) → ((True ∧ p5) ∧ p4)))) ∨ (False ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319280505981880307851091526038 : (p4 ∨ ((((False ∨ True) ∨ p2) → (((False ∨ p5) ∧ (((True ∨ False) ∧ p4) ∧ p5)) ∨ True)) ∨ (p1 → (((False ∨ (p4 → False)) ∧ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- False on the left can always be used.
      apply False.elim h3
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206256576396380550181993177593 : ((False ∨ (((p5 ∨ p2) → p4) → False)) ∨ (((((((True → p4) ∨ p1) ∨ True) → p1) → ((False ∨ (p4 ∨ (p1 → True))) ∨ p4)) ∧ False) → False)) := by
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
theorem thm_5_vars_611735519420887165619424154024 : (((((True → ((((p5 ∧ p3) ∧ p3) ∧ (p5 ∧ p2)) → (p3 ∨ (((p2 ∧ ((p5 ∨ True) → (p4 → p1))) ∨ p5) ∨ p3)))) → p2) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44812332100347204312954717725 : ((((p4 ∧ (p5 → p2)) ∧ (p2 → (True ∨ (p1 ∨ ((True ∨ p3) ∨ ((p3 ∧ (((p5 ∨ True) ∨ p1) ∨ (p3 → p4))) ∨ True)))))) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_710147633301996225079660418033 : ((((((p5 ∧ (p2 ∧ p4)) ∨ p3) ∨ True) ∧ ((((p5 → (p2 ∧ False)) ∨ (p5 → (((p3 ∨ (p5 ∨ p1)) → p5) → p3))) → p1) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734534711017888878382838345555 : ((((p1 ∨ p1) ∧ ((((((p2 → p2) ∨ p4) ∨ (((p1 → p1) ∧ True) → (p4 → True))) ∧ (True → p4)) ∨ (p1 → p3)) ∧ (p2 ∨ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39176779769004996721580915490 : ((((p1 → True) → ((((((p5 ∨ p3) ∧ p4) ∨ ((False ∧ p1) ∨ (True → p4))) → p5) ∨ ((p3 ∧ (p4 → p1)) → False)) ∨ False)) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229864794874589416592941501505 : ((p5 → (p1 ∨ p1)) ∨ (((p1 ∧ (((p1 ∨ True) ∧ p4) → p2)) ∨ p5) ∨ (((p2 ∨ p4) → p5) → (p5 → (p4 → (False ∨ (p5 ∨ p5))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64409490898601380759375914952 : ((p1 ∨ ((((p1 → p1) ∨ p1) → ((p5 → ((p3 → (p1 ∨ p5)) ∨ p1)) ∧ ((((p3 ∧ False) → (p5 ∨ p3)) ∧ False) ∧ p3))) → p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 → p1) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190199185553362633749866268725 : (((p3 ∨ (False ∧ ((p5 ∨ (p5 ∨ p5)) ∧ p3))) ∧ False) ∨ ((True ∨ p4) ∨ ((((((True ∨ False) ∧ p4) → (p1 ∨ p4)) ∧ p3) ∨ p2) ∧ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114829808660152701264430201626 : (((p5 ∨ ((p2 ∨ True) → (((p3 → ((p4 → False) ∧ p3)) ∧ p1) ∨ p4))) ∧ ((((True → (p4 → p2)) → p1) ∧ p3) ∧ p2)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



