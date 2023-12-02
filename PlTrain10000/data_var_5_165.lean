variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340732851296684114583696423922 : (p2 → ((((((p1 ∨ (p5 → (p3 → (((True ∨ p2) ∧ p3) → (p2 ∧ False))))) ∨ ((p4 ∨ p2) ∧ p5)) → (p5 ∨ p1)) ∨ False) ∨ p2) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111934764124495431731412629556 : (((((p4 ∨ (((p2 ∨ True) ∨ p1) → p5)) ∧ (p3 ∧ p2)) ∨ (p1 ∧ (False ∧ (False ∨ (False → ((p3 ∨ True) ∧ p3)))))) ∨ True) ∨ (p2 → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40317487791542366475385952641 : (((((p4 ∧ (((False ∧ (((p2 ∨ (p1 ∧ (False ∧ True))) ∧ (True → p1)) ∨ (p3 → p3))) ∧ p3) ∧ (p4 ∧ p4))) ∧ p4) ∨ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191536372720703867442083345906 : ((p1 ∧ (((p1 ∧ (p3 ∨ p1)) ∨ (p2 → p5)) ∨ p3)) ∨ ((p2 → p5) → ((False → ((((False → p3) ∧ p2) ∨ p5) ∨ (p2 ∨ False))) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172840197262544884952243117861 : ((False ∧ ((True → ((p3 → (True ∧ (p3 → p1))) → (p1 ∨ (p3 ∧ p2)))) ∨ p4)) ∨ ((p4 → p2) → (((True ∧ p1) ∧ p5) → (p1 ∧ p1)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h2.left
  let h8 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- One of the premise coincides with the conclusion.
  exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_169508098356606684746336049733 : (((True ∧ ((((p4 ∨ (p2 ∨ p1)) ∨ (p2 → True)) ∨ p4) ∨ (p5 → p2))) ∨ p2) ∧ (True ∧ (False ∨ (p5 ∨ ((p2 → p2) ∨ (True → p3)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53746500406697693068646160705 : ((((((p4 ∨ (p5 ∧ (p3 → p5))) ∧ p2) ∨ p5) ∧ p5) ∨ (True ∨ (p3 ∧ ((p3 → (((p1 ∨ False) ∨ p2) ∨ (True ∨ False))) → p2)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321737572813827396077457240438 : (p4 ∨ (p5 → ((False ∧ ((p1 ∨ (p1 → p5)) ∧ ((p1 ∨ p1) ∨ (p1 ∨ ((p5 → p4) ∧ p3))))) ∨ ((p5 ∧ p1) → (p3 ∨ (p1 ∧ p5)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205917452182718857083367273912 : ((False ∧ ((True ∧ (False ∧ p2)) ∧ p5)) ∨ ((((p1 ∧ p1) → p1) ∧ p2) ∨ (((p2 → p4) → True) ∨ ((True → p5) → ((p5 ∨ p4) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117081398093107276094074316585 : (((False → p1) → ((False ∨ p3) ∨ ((p5 ∨ (False ∧ ((((True ∧ (p4 ∨ (True ∧ p2))) ∨ (p5 ∨ True)) ∨ True) ∧ p5))) → False))) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208187267584816321700534473955 : (((p1 ∨ (False → p3)) → (False ∧ p2)) → ((((p4 ∨ ((False ∨ p3) → p2)) ∧ ((p4 → p3) → True)) ∧ p2) → ((p4 → (p1 ∧ p5)) ∨ p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p1 ∨ (False → p3)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_659840315823733853912941702074 : (((((True → (((p3 ∧ False) ∧ (p4 ∨ ((((p5 ∧ (p3 ∨ p1)) → p5) ∧ False) → p2))) → ((p5 → p4) ∨ False))) ∧ True) → (p4 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_793881372278716652295904714126 : (((True → (p4 → ((((False ∨ ((p3 → ((p5 ∧ ((False → p4) ∧ ((p2 ∧ p2) ∨ True))) → (False ∨ p5))) ∧ p5)) ∧ p3) ∨ True) ∧ p4))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172274705183484952502266117144 : (((((p1 ∨ p3) ∨ False) → ((True → p2) ∧ True)) ∨ ((p5 → (p3 → False)) ∨ p3)) ∨ ((p5 ∨ ((True ∧ p3) → True)) ∧ ((p3 ∧ p4) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66838068443611617761269603957 : ((True → (p2 → ((True ∨ p4) → ((((((p2 ∨ (p4 → (p3 ∧ p5))) ∨ p2) → p4) ∧ p1) → p5) → (True → ((p3 ∧ True) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140497855665077966002127882531 : ((((((p5 ∨ (p1 ∧ False)) ∧ ((p3 → False) ∧ p3)) → True) → (False ∧ (p1 ∧ p2))) ∧ (((p5 → p1) ∨ p4) ∨ False)) → ((p3 → p2) ∧ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
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
      have h7 : (((p5 ∨ (p1 ∧ False)) ∧ ((p3 → False) ∧ p3)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h8
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h9 := h3 h7
      -- We need to get the left conjuct of h9 based on <expert-advice>.
      let h10 := h9.left
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : (((p5 ∨ (p1 ∧ False)) ∧ ((p3 → False) ∧ p3)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h14 := h3 h12
      -- We need to get the left conjuct of h14 based on <expert-advice>.
      let h15 := h14.left
      -- False on the left can always be used.
      apply False.elim h15
  case inr h16 =>
    -- False on the left can always be used.
    apply False.elim h16
  -- Conjunctions on the left can always be decomposed.
  let h17 := h1.left
  let h18 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h18
  case inl h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h21 : (((p5 ∨ (p1 ∧ False)) ∧ ((p3 → False) ∧ p3)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h22
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h23 := h17 h21
      -- We need to get the left conjuct of h23 based on <expert-advice>.
      let h24 := h23.left
      -- False on the left can always be used.
      apply False.elim h24
    case inr h25 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h26 : (((p5 ∨ (p1 ∧ False)) ∧ ((p3 → False) ∧ p3)) → True) := by
        -- Implications on the right can always be decomposed.
        intro h27
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h28 := h17 h26
      -- We need to get the left conjuct of h28 based on <expert-advice>.
      let h29 := h28.left
      -- False on the left can always be used.
      apply False.elim h29
  case inr h30 =>
    -- False on the left can always be used.
    apply False.elim h30



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165903477086982451234695248987 : (((p2 ∨ (p2 → p3)) → ((((((False ∧ p2) → p4) → False) ∨ True) → p1) ∨ (True ∧ p3))) ∨ (p4 ∨ ((p4 → True) ∨ ((p4 ∨ p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_107367580138337316695944564476 : (((p5 ∨ (p2 ∨ p4)) ∨ (p3 ∨ ((p1 ∨ (p5 → ((p2 ∧ (p3 ∨ (True ∨ p3))) ∧ (p2 ∨ (p2 → True))))) → (False → p3)))) ∧ (False ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157736345219664044984234739692 : (((p4 → ((p4 ∨ (p5 ∧ True)) → ((p4 ∧ p1) ∨ (True → (p4 ∧ p2))))) → ((p4 ∧ True) ∨ p5)) ∨ (p4 → (False → ((p4 ∧ p5) → p1)))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729854925362350632819707992497 : (((((False ∧ p5) → p3) → (p3 ∧ (((((False → p1) ∧ (p4 → p5)) → (p4 ∧ p3)) → False) ∧ ((p4 ∧ (p3 → (p2 ∧ False))) ∧ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50814355883835396571669423984 : (((p4 → ((((p3 ∨ (False ∨ (p2 ∧ p5))) → (((p3 ∨ p2) ∧ p1) ∨ (p1 ∧ p2))) ∧ p4) ∨ p5)) → ((False ∨ (True ∨ p3)) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55697334173697886403269136503 : ((((False ∧ (p2 ∨ p1)) ∨ p5) ∧ (p1 ∨ ((p2 ∧ ((False ∨ ((((p3 ∧ False) ∧ p4) ∧ p2) ∧ p4)) ∨ (p4 ∧ (p3 ∧ p1)))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606535109081720182541620605085 : (((((((p2 ∨ (((p4 ∧ (p1 ∧ (False → p1))) ∧ p4) ∨ ((((p5 → p4) ∧ p1) → False) → p1))) ∨ (p4 → p1)) → p1) ∧ p5) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314251028675655889000640396478 : (p3 ∨ (((((p2 → (((True ∨ p1) → p4) ∧ (True ∧ p2))) ∨ p2) → p3) ∨ (True ∧ (((p3 → p1) → p4) ∨ p1))) ∨ (p4 ∨ (p5 → True)))) := by
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
theorem thm_5_vars_389780377692191878821415906955 : (((((((p1 → p1) ∧ (False ∧ p1)) ∨ (p2 ∨ ((p2 ∨ p3) → p1))) ∨ ((p1 ∨ p5) → (p3 ∧ ((p2 → (True ∨ p5)) ∨ True)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_211361499023481505130331736022 : (((p5 ∨ False) ∨ (True ∨ p5)) ∧ ((((p5 ∧ (p1 ∨ p5)) ∧ (False → (((((p1 ∨ (False → p3)) → True) ∧ p5) ∨ p3) → p3))) ∨ True) ∨ p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164841024678846919124151842003 : (((p3 ∧ ((((p2 ∨ False) ∨ (True ∧ (p5 → p5))) ∨ (p4 ∨ (p2 → p4))) ∧ False)) ∨ p3) ∨ (True ∨ ((p4 ∨ (p2 ∧ p5)) ∧ (p5 ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304985146288654900709206144024 : (p1 ∨ ((((p5 ∧ True) ∨ (((p2 → (((p3 ∧ False) ∧ p2) → p1)) ∧ (p1 ∧ (p1 → (p3 ∨ p4)))) ∧ p1)) ∨ p4) ∨ (p2 ∨ (True ∨ p4)))) := by
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
theorem thm_5_vars_215321860043976892775874432849 : ((p1 ∧ (p2 ∧ (False → p1))) ∨ ((((((False ∧ p5) ∧ p4) → ((p5 → p1) ∨ p2)) → True) ∧ p3) ∨ (p5 ∨ (True → ((p2 ∨ True) ∨ False))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158148585913531619873218956570 : (((p2 ∧ (p2 → (True ∧ p4))) ∨ (p2 ∧ (((p4 ∧ ((p2 → True) ∧ p3)) ∧ False) ∧ (p2 ∨ True)))) ∨ (p1 → (p2 ∨ (p3 → (False → p1))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653933317658916871933818103818 : ((((((p3 → p4) ∨ ((False ∨ (p2 ∧ (p3 → (False ∧ ((p5 ∧ (p2 ∧ False)) ∨ False))))) → ((False ∨ True) → p3))) ∧ p3) ∨ (p5 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_624502666147558082455129595652 : ((((p4 ∨ (((((p2 → ((p2 ∧ p1) ∨ p4)) ∧ ((p2 ∧ p5) → p4)) → (p2 ∨ p1)) → (p4 → ((p2 ∨ p1) ∨ p2))) ∨ False)) ∨ False) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((p2 → ((p2 ∧ p1) ∨ p4)) ∧ ((p2 ∧ p5) → p4)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h3
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121710741719859060377820756540 : ((((p1 ∧ (p5 ∨ (((p1 → False) ∨ p5) ∧ p3))) ∨ ((True ∧ (p2 ∨ True)) → ((True ∨ p2) ∧ (False → (p2 ∧ True))))) → False) → (True ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p1 ∧ (p5 ∨ (((p1 → False) ∨ p5) ∧ p3))) ∨ ((True ∧ (p2 ∨ True)) → ((True ∨ p2) ∧ (False → (p2 ∧ True))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h2
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37701298587113494959513294505 : ((((((((((p5 ∨ p3) ∨ p1) → ((False → p2) ∨ p3)) ∧ (p3 ∨ False)) ∧ p5) ∧ (p1 → True)) ∨ ((True ∨ p1) ∧ p4)) → p1) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_504890398659058439270030390771 : ((((p5 ∨ (p4 → p3)) → (((p4 ∧ (p3 → (p4 ∨ (p2 → (False ∨ True))))) → (True → ((p3 → p5) ∨ (p5 ∧ p4)))) ∨ (False → False))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_786289496432168929922503749548 : (((p4 ∨ (((p2 → (p3 ∨ (((p4 ∨ (p1 ∧ p2)) ∧ (((p2 → p5) → p4) ∧ p2)) ∨ p4))) ∨ p2) → (((p1 → p1) → p5) ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148589212069996728068013534804 : (((((p1 ∧ p1) ∧ (p1 ∧ p5)) ∨ ((p3 ∨ False) ∨ p1)) ∨ ((((False → (True → p1)) ∧ p2) ∧ p2) ∧ True)) ∨ ((p2 → True) ∨ (p1 ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725259418565719188797352860958 : ((((p3 → (False ∧ p4)) ∧ (((p1 → (p3 → (p4 ∧ (p5 ∨ p1)))) → p3) ∧ (((p2 → ((False ∨ p1) ∨ (p3 → True))) ∧ False) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180265110573648558785038527234 : (((p5 ∨ (False ∨ ((p4 ∨ p2) → (((p1 ∧ False) → p5) ∨ p3)))) → p5) → ((p4 → ((p2 ∨ (((p4 ∨ p2) ∨ p2) ∧ p2)) ∨ p4)) ∧ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p5 ∨ (False ∨ ((p4 ∨ p2) → (((p1 ∧ False) → p5) ∨ p3)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
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
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h13 := h1 h3
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90995265308641434111582696262 : (((p1 → True) ∧ ((True ∨ p1) → (((p3 → (((p4 ∧ ((p1 → p1) → p2)) → p5) ∧ (True → ((False ∧ p5) → p2)))) ∨ True) → False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (True ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : ((p3 → (((p4 ∧ ((p1 → p1) → p2)) → p5) ∧ (True → ((False ∧ p5) → p2)))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52613670444111420036461660704 : ((((p4 ∧ (p3 ∨ (p1 ∨ p3))) → ((((False → p2) ∨ p5) ∧ p5) ∧ p3)) ∨ (((((p5 ∧ (p5 ∧ p4)) → p1) ∧ True) → p3) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147466088965306503060696589032 : (((False ∧ (((((True ∨ p5) ∧ ((p2 ∧ (True ∧ p5)) ∨ (p1 → p3))) → p4) ∧ (p3 → p3)) ∧ p3)) ∨ True) ∨ ((False → p5) ∧ (False → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200267530264045823091818185223 : (((False ∨ (p2 → p5)) → (False → (p5 → p3))) → ((((((p1 ∧ p1) ∨ p4) → (((p4 → p1) → p1) ∧ False)) ∧ (True → False)) → False) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725741006262921289057964751841 : (((((p1 ∨ p5) ∧ p5) ∨ (((p1 ∨ (((p3 → (p4 ∧ p2)) → ((((p2 ∧ p5) ∧ p1) ∨ True) ∧ (p2 → False))) ∨ False)) → p1) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_121622638105811480554386849695 : ((((((False → p5) ∧ ((p3 ∨ ((p2 ∧ (p5 ∧ p3)) ∨ p4)) ∧ True)) ∨ (True ∧ p2)) ∨ ((p5 ∨ True) ∨ (False → p1))) → p1) → (p1 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((False → p5) ∧ ((p3 ∨ ((p2 ∧ (p5 ∧ p3)) ∨ p4)) ∧ True)) ∨ (True ∧ p2)) ∨ ((p5 ∨ True) ∨ (False → p1))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149373343922732043186925648731 : (((p1 → p5) → ((((p1 ∧ p1) → p3) ∧ p2) ∧ (False ∨ (p3 ∧ (p4 ∧ (p1 ∨ (p4 → (p5 ∧ True)))))))) ∨ ((p1 → (p4 → p4)) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701532493162754755571443825738 : (((((p4 ∧ (p2 ∨ True)) → (p5 ∨ (True ∨ (p4 ∧ p5)))) ∧ ((((p2 ∧ True) → (True ∨ (p3 ∧ p2))) ∧ p5) ∧ ((False ∨ p2) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338541623170339421026965262634 : (p1 → ((p3 ∧ (False ∨ p5)) ∨ (((((p5 → (p2 → p3)) → (p2 ∧ ((p3 → False) → ((p2 ∧ p1) ∨ True)))) ∨ (p4 ∨ p3)) ∨ False) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233841677207697059224811352266 : ((p4 ∨ (p1 ∧ p3)) → ((p5 → (((p2 ∨ p5) ∧ (p1 ∧ ((p4 ∧ (p3 → False)) ∨ p1))) ∨ (((p1 ∨ (p2 ∨ True)) ∨ p4) ∨ True))) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678080676298476966214216652653 : ((((((p2 → ((p4 → (p4 → True)) → p4)) → ((p2 ∧ True) ∨ (p5 ∨ p1))) → ((p2 → p5) ∧ p1)) ∨ (((p4 → p1) ∧ True) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65201919048639591950297759633 : ((p3 ∨ (((False ∧ (((((True → (True ∨ p1)) → p3) ∧ p4) ∧ p4) ∧ (((False → ((p3 ∨ p4) ∧ p5)) ∨ p2) → p3))) ∨ True) ∨ p1)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344186324787378753570822066363 : (p2 → (p1 ∨ ((p2 → (((p4 ∨ p3) ∨ p3) ∨ (p5 ∨ ((p5 ∨ (p2 → True)) → p1)))) ∨ ((p2 → (p3 ∧ (p2 ∨ (p4 → True)))) → p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804652575265587159326279632442 : (((p3 → ((((p3 ∧ p4) → True) → False) → (((p2 → p3) → (p2 ∨ (False → False))) → (((p2 ∧ ((True ∨ p2) ∨ p5)) ∨ p4) ∨ p4)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p3 ∧ p4) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327161710131805268881926390738 : (True → ((p5 ∧ ((p2 → (True ∧ (((False → False) ∧ (p5 ∨ (True ∧ (True ∧ ((p4 ∧ ((p3 ∨ p1) ∨ False)) ∧ p1))))) ∨ p3))) → p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685867459652218861145168968550 : (((((False ∧ (((False → p4) ∨ (((p3 → False) ∧ (p2 → p2)) ∨ p2)) ∧ (p1 → p5))) → p5) → ((p4 → p5) ∨ (True → (p1 → p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45510044225319567424453371183 : (((p1 ∨ ((((p2 ∧ (True → True)) ∨ ((p2 ∧ p3) ∧ True)) ∧ (p1 → (((p4 ∨ (p2 → p2)) → (p5 → p4)) → p1))) → p2)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118762695623129992067496739526 : ((p5 ∨ ((False → p5) → ((((p1 ∨ ((True ∨ p4) → p3)) ∨ False) ∧ False) ∨ ((False → ((p5 → (p5 ∧ p2)) ∧ True)) ∨ p2)))) ∨ (p3 ∧ p5)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729196967480794406063958120955 : (((((p3 → p1) ∧ p3) → (((((((p4 ∧ False) ∧ ((True → p1) ∨ (False ∧ ((False ∨ p3) ∨ p2)))) → False) ∨ p2) → False) ∨ p1) ∨ True)) ∨ p4) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46298133150016262078999380638 : ((((((False → p4) ∧ (((((p3 ∨ (p3 → (True → p3))) ∧ p1) → p2) ∧ True) ∨ False)) → p4) → (p1 ∧ (p4 ∨ False))) ∧ (p2 → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112072783302367058220659057427 : ((((p4 → p4) ∧ (p3 ∨ (((((False ∨ p4) → (False ∧ (p2 ∨ (True ∧ (True ∨ (p3 → p4)))))) ∨ p2) ∧ p2) ∧ p3))) ∨ False) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242973087010991731535907624698 : ((p4 → True) ∧ (((((p5 ∧ (((p2 ∨ (((p4 ∨ (p4 ∧ p2)) ∨ (p4 ∧ True)) ∧ p2)) ∧ p5) ∨ (p3 ∨ p4))) ∧ p1) ∨ False) ∨ True) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678890532825495224664833124666 : ((((p2 ∧ ((p2 ∨ ((p4 → p1) → p3)) ∨ ((((True ∨ (True → (p2 → p3))) ∨ p5) → p5) ∧ True))) ∨ (False ∨ (p4 → (p1 ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42259411425062061623899801442 : (((p1 ∧ (((True → p5) ∨ ((((p4 ∧ ((p3 → p2) ∧ True)) ∨ ((p3 → True) ∧ ((p2 ∧ p3) → p3))) ∨ p5) → True)) → p4)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265710339332446360496602157906 : (True ∧ (p3 ∨ (((((p4 ∨ p3) ∨ (p3 ∧ True)) ∧ True) → ((((True ∧ (p4 ∨ False)) ∨ (False ∧ p3)) ∨ p3) ∨ p1)) ∨ (p2 ∨ (False ∧ p2))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136020844192489136238172973548 : ((((p3 ∨ (((p1 → p4) → (p2 → p1)) ∨ False)) → True) → ((((True → (p4 ∧ p2)) ∧ (True ∧ p4)) ∨ p3) ∧ False)) ∨ ((True ∨ p2) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_692143656051707293284959394097 : (((((((p1 ∧ (p2 ∧ p1)) ∧ (((True ∨ False) ∧ p3) ∨ p2)) ∧ p2) ∨ p5) ∧ ((p5 → (p1 → (p4 ∨ ((p2 ∧ p1) ∧ p3)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117354425175259321080105806271 : ((False ∧ (p4 ∧ ((p4 ∨ (((((((True ∨ (p1 ∧ True)) ∧ (p1 → False)) ∧ p3) ∧ True) → p1) ∨ False) → (False ∧ p4))) ∧ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_243936516363206984108031092279 : ((True ∧ False) ∨ (p3 → ((p5 → (((p1 → p2) → (((p2 ∧ p2) → (p1 ∧ p1)) ∧ p1)) ∨ True)) ∨ ((p2 → ((p5 ∧ p3) ∧ True)) ∧ True)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709585288801521799533195365897 : ((((p1 ∨ ((((p4 ∨ False) ∨ p4) ∨ p4) → True)) → (((p1 ∧ (p4 → (True ∨ (p3 ∨ p2)))) ∨ p1) ∧ (((p2 ∧ True) → p3) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190886043363287766071203248958 : ((((p4 ∨ p4) → (p4 ∨ (p3 ∧ p4))) → (p4 ∨ p2)) ∨ ((True ∨ True) ∧ (p3 → (p3 ∨ (p1 ∧ ((p1 ∧ ((p3 → p4) ∧ p3)) ∨ p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38741382018971986157973251341 : ((((((p4 → True) → False) ∧ p2) ∧ ((p2 ∨ (p5 ∨ (((True → ((p4 ∧ p4) ∧ p2)) ∨ p4) ∧ (True → p2)))) ∧ (p3 ∨ True))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225673068309770469064924037816 : (((p2 → p4) ∧ p5) ∨ ((((False ∧ ((p3 ∧ p3) → (((p4 → (False ∧ False)) ∨ p3) ∨ p5))) ∧ p5) ∨ True) ∧ (p1 → ((p1 ∧ False) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655191557605002410593635963635 : (((((((p3 → p2) ∧ (p4 ∧ ((p1 ∧ ((p1 → ((p2 → p3) ∨ (p3 → False))) ∨ p2)) ∧ False))) ∧ p4) ∧ (p1 → p3)) ∨ (False → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152165568264162942478940198795 : (((p3 ∨ (p2 ∧ (False → ((p5 ∧ p3) ∧ p2)))) ∨ (p1 → ((((p1 ∨ p3) ∧ p2) → p4) ∨ (p2 → p5)))) → ((False ∨ p4) ∨ (False → False))) := by
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
      -- False on the left can always be used.
      apply False.elim h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150870106834695937390907358357 : (((((p1 ∧ p1) → ((p1 → False) ∧ p4)) ∧ ((p5 ∧ (((True → p5) → (p3 ∧ p3)) ∧ True)) ∧ p1)) ∨ p2) → ((False → p4) → (p2 ∨ False))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h12 : (p1 ∧ p1) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h7
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h13 := h4 h12
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
    have h15 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h14, we can now drive its conclusion.
    let h16 := h14 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666145190803863363462128042637 : ((((((p1 → ((p5 ∧ p5) ∨ (((p3 ∨ p2) ∨ (p5 ∧ ((p2 ∨ p2) ∧ p3))) ∧ p3))) ∧ p5) ∨ (False ∧ p5)) ∧ (p3 ∧ (True ∨ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138744655416014829454790065745 : (((((True → p3) ∨ False) ∧ (p3 ∧ (((p5 ∧ (False ∧ False)) → p5) → (p3 → (((p4 ∨ p3) → p5) ∧ p4))))) ∧ True) → ((p2 → p4) ∨ True)) := by
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
    let h7 := h5.left
    let h8 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191222803943017772961375599793 : (((False ∨ (True ∨ p3)) → ((False ∧ (False ∧ p5)) ∨ True)) ∨ ((p2 ∨ p2) ∨ ((p5 ∧ p2) → (p4 ∧ (((p1 ∨ p4) ∧ (True ∨ p1)) → p1))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_701730879290493738915046829410 : ((((False ∧ (((True ∨ p1) → (True ∧ (True → p4))) → p2)) ∧ ((p4 → (((False → True) → ((p1 → p4) → (p3 ∧ p3))) → p3)) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200029546655060271108048296507 : (((False ∧ ((p3 → p1) ∧ p1)) → (p5 → p3)) → ((p1 → (False ∨ p2)) ∨ ((((True ∧ ((False ∨ (True ∧ False)) ∨ True)) ∨ p4) ∧ False) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- False on the left can always be used.
        apply False.elim h12
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h4
  case inr h14 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41124924071198090881003597781 : (((((((p3 ∧ (p2 → True)) ∨ ((((False ∧ True) → p5) ∨ p2) → p4)) ∧ (p3 ∧ (True ∧ p5))) ∧ p3) ∨ ((p5 ∨ p4) ∨ True)) ∨ False) ∨ p2) := by
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
theorem thm_5_vars_151057221134316417677000950958 : ((((p4 → ((p3 ∧ False) ∧ ((p1 → (p1 ∨ (p4 ∧ ((True → True) ∨ (p2 ∨ p2))))) → p1))) ∧ p5) → False) → (((p1 ∨ p3) → p5) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167475178383932273099062302527 : (((p5 → (((False ∨ (p4 ∧ (False ∨ p5))) ∧ False) ∧ (p1 ∨ (p2 → (p4 ∧ True))))) → False) → ((((p2 → (p3 ∨ p1)) ∨ p4) → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602627887386030256451638772744 : ((((False ∨ (((p5 → ((p1 → ((True ∧ p2) ∧ True)) ∧ (p3 → ((p3 ∧ False) ∧ p2)))) ∨ (p5 ∨ (True ∨ True))) → (p1 ∧ p4))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47321751091949041995929061003 : (((((p4 ∧ p1) → p3) → (((((p4 ∧ p4) → (True ∨ p4)) ∧ False) ∨ ((p2 → True) ∧ (p1 ∨ p1))) ∧ (True → p5))) ∨ (True → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_388909340786374074413465106654 : (((((p3 → ((((p2 → p3) ∧ False) ∨ p5) ∨ ((p3 ∧ False) ∧ (False ∧ (True → p5))))) ∨ ((p5 → p4) → (p5 → (p1 ∨ p1)))) ∨ True) ∧ True) ∧ True) := by
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
theorem thm_5_vars_171601736535084363403877388771 : ((((((p1 ∨ p2) ∨ p1) ∧ (p2 → p5)) ∨ (p5 ∨ (p2 ∧ (p1 → p3)))) ∨ False) ∨ (p2 → (((p1 → ((False ∨ False) ∧ p1)) ∧ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617822153719946342544320531385 : (((((((True ∧ p5) ∧ (p1 ∨ p2)) ∨ p5) → (((False → (False → (p1 → (((True ∨ False) → False) ∧ (p3 ∧ p2))))) ∨ p4) → p3)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55600829349133495930391178883 : (((True → ((False ∨ (p5 ∨ False)) → p4)) → (p4 ∨ ((((p4 ∧ p1) → (p5 ∨ p5)) ∧ ((p1 ∨ (p2 ∧ p2)) → p4)) ∨ (p5 → p4)))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : (False ∨ (p5 ∨ False)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678015622119386717832828261848 : (((((p2 ∧ (((p1 ∧ p4) → (True ∨ (p1 ∧ (p5 → (p3 → p3))))) → p1)) ∧ (p3 ∧ (True ∨ p3))) ∨ ((False → (p2 ∧ p4)) → True)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_262165685956569472121324806127 : (True ∧ (((p1 ∧ ((False ∨ ((True ∧ ((p1 ∧ True) ∧ p1)) ∧ (p3 ∨ (False ∨ ((p1 ∧ p5) ∧ p1))))) ∧ ((True ∧ p5) ∧ p1))) ∨ p4) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727438581338781522306252922941 : ((((p3 ∧ (p5 ∧ p5)) ∨ ((p2 ∨ p5) ∨ (p5 → (((p5 ∨ p4) ∨ (((p3 ∨ p2) ∨ p4) → p3)) → (True ∨ ((False ∧ p1) → False)))))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110526347583531116018289514335 : ((p4 → ((((p4 → p1) ∧ p2) ∨ True) ∧ ((((p3 ∨ (p4 ∧ (p2 ∧ (p2 → False)))) → False) ∨ p3) ∨ ((p4 ∧ p2) ∨ p4)))) ∧ (True → True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781557322920455809281478366694 : (((p2 ∨ (False ∨ ((((False ∧ p2) ∨ (((p2 → (((p3 ∨ (True → False)) ∧ (p3 → p4)) ∨ p3)) → p5) → p1)) → p1) ∨ (p2 ∨ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301362396879223970610428742868 : (False ∨ (((p3 ∨ (True ∧ False)) ∧ p4) ∨ (p2 ∨ (True ∨ ((p3 ∨ (p3 ∧ p4)) ∨ ((False → (((p3 → (False ∧ False)) → p3) ∧ True)) → p2)))))) := by
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
theorem thm_5_vars_315111938015925344075441289250 : (p3 ∨ ((((p5 ∧ p4) ∨ (p5 ∧ p3)) ∨ True) ∨ ((((p5 ∧ ((((p3 ∧ p3) ∧ (p3 → (p1 ∧ p4))) ∨ p1) ∧ p1)) ∧ p3) → False) ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307755387695251557277635070243 : (p1 ∨ (p3 → (((p4 ∨ p3) ∧ (p5 ∨ p2)) ∨ (((((((p3 → p1) ∧ (p1 ∨ p2)) ∧ p2) ∨ ((True ∨ p1) → False)) ∨ True) ∨ p3) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_229532948223571054170169866252 : ((p2 → (p5 ∨ p1)) ∨ (((p5 → ((p5 → (((True → p5) ∨ p5) ∧ p2)) ∧ ((p2 ∨ p3) ∧ p4))) → False) ∨ (False ∨ (p4 → (p5 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227802259386913139813309986046 : ((p1 ∧ (p5 → p2)) ∨ (p2 → ((False ∧ (False ∨ (p4 ∨ (p3 ∨ (((p1 ∨ p5) ∧ (p4 ∨ (p4 → p3))) ∧ p3))))) ∨ ((p1 ∧ p1) ∨ p2)))) := by
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
theorem thm_5_vars_46720105135782778977172644511 : (((p5 ∨ (p2 ∧ (p1 → (p5 → ((((((p4 ∨ (p2 ∨ (p5 ∧ p4))) → False) → (p1 → False)) ∧ p4) ∧ True) ∨ p3))))) ∧ (True ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



