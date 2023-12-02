variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691622939300019477980309554705 : ((((p3 ∧ (((p5 → p2) ∧ p4) ∨ ((p3 → (p5 ∧ p4)) ∧ (p4 ∧ (p4 → p4))))) → (((p5 ∧ True) ∧ (p3 ∧ (p4 ∨ p5))) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206307102365032012103038915965 : ((p1 ∨ ((p1 ∧ False) ∧ (p2 ∧ p2))) ∨ (((((False ∨ p3) → ((True ∧ p4) ∨ p4)) ∨ (p5 → p4)) ∨ True) → (p2 → ((p2 → True) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32021125509170615065945681607 : ((p1 ∨ ((p1 → (p2 ∧ (((((p1 → (p5 ∧ ((p5 → p2) ∧ p5))) → p4) ∨ ((p4 ∨ (p4 → p5)) ∧ p2)) ∧ p3) ∧ p4))) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_171962923994623174384554117825 : ((((p2 ∨ p3) ∨ (p3 → ((False ∨ p5) ∧ (p2 → (False ∧ False))))) ∧ (p2 ∧ True)) ∨ (((((p2 → p5) ∨ p4) ∨ (p2 → p1)) ∧ False) → p2)) := by
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
      apply False.elim h3
    case inr h6 =>
      -- False on the left can always be used.
      apply False.elim h3
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_905155609315489189959819745395 : (((((p3 ∨ p5) ∧ (True ∧ (False ∨ (((((True → (p3 ∧ p1)) ∧ p1) → p1) → (p4 ∧ False)) ∧ p4)))) ∨ (True → ((p2 ∧ p3) ∧ False))) → p5) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h4.left
      let h7 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h8
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h12 : (((True → (p3 ∧ p1)) ∧ p1) → p1) := by
          -- Implications on the right can always be decomposed.
          intro h13
          -- Conjunctions on the left can always be decomposed.
          let h14 := h13.left
          let h15 := h13.right
          -- One of the premise coincides with the conclusion.
          exact h15
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h16 := h10 h12
        -- We need to get the right conjuct of h16 based on <expert-advice>.
        let h17 := h16.right
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h4.left
      let h20 := h4.right
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h25 =>
    -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
    have h26 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h25, we can now drive its conclusion.
    let h27 := h25 h26
    -- We need to get the right conjuct of h27 based on <expert-advice>.
    let h28 := h27.right
    -- False on the left can always be used.
    apply False.elim h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204102250640409494394687213982 : (((((False ∧ p5) ∧ p5) ∧ p4) ∧ p2) ∨ ((p4 → (False → (((p5 ∧ (False ∧ True)) ∨ (True ∨ p5)) → ((p1 ∨ p4) ∨ p1)))) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22135598981370713621812911140 : (((((p4 ∨ False) → p1) ∧ (p5 ∨ (p5 ∨ p1))) ∨ (((((p4 → p2) → (p5 ∨ p2)) ∧ p2) → ((True ∧ (p4 ∨ False)) ∧ p5)) ∨ True)) ∧ True) := by
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
theorem thm_5_vars_353656873961285559357509129957 : (p4 → (p5 ∨ ((p5 ∧ ((((((p5 → (p4 ∧ ((True → p5) ∧ False))) ∧ p1) ∨ ((p1 ∨ True) → p1)) ∧ p5) ∨ (True ∨ p4)) → False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49107977810693624056362197268 : (((((False ∨ ((p5 ∨ p3) ∨ (p3 → (p2 ∧ p1)))) ∨ (p4 → (p3 ∨ p3))) ∧ (p2 ∨ ((p1 ∨ True) ∧ p1))) ∨ ((p5 ∧ False) → p3)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_41249455961574868726191077102 : (((((((False ∧ p4) ∨ p5) ∨ ((((p3 ∨ p5) → p1) → p3) → ((p1 ∨ p5) ∨ p5))) → p5) ∨ (((p2 ∧ True) → p4) → p3)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314639708714569940324677109722 : (p3 ∨ ((((p2 ∧ (p1 → p5)) ∨ (((((p2 ∧ p2) ∨ p5) → False) ∧ p4) ∨ p1)) ∧ p5) ∨ (((False ∨ ((p1 ∨ p3) → p5)) ∨ True) ∨ p1))) := by
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
theorem thm_5_vars_56839679077071493708906382764 : ((((p5 → True) → p4) ∧ (((p4 ∧ p5) ∨ ((True → (p3 ∨ ((True → p3) ∨ p2))) ∧ (p3 ∨ (True ∧ (p4 ∨ True))))) ∧ (True ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625571545251580677655640308756 : ((((p1 → (((((p1 → False) ∨ ((p2 ∨ p4) ∨ p2)) ∨ (((((p2 → p5) → False) ∧ False) ∧ (True ∨ p5)) ∨ p3)) ∨ False) ∧ p1)) ∨ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80303218563252140747453470640 : (((((p2 ∧ (False → (False ∨ (p4 → (p1 ∨ p2))))) → (p4 ∧ ((p4 ∧ p2) → (p5 → p1)))) ∨ (True ∨ (p2 ∧ p2))) → (p2 ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∧ (False → (False ∨ (p4 → (p1 ∨ p2))))) → (p4 ∧ ((p4 ∧ p2) → (p5 → p1)))) ∨ (True ∨ (p2 ∧ p2))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613544318982311980618793352684 : ((((((p4 ∧ (((p4 → (p1 ∨ (p1 ∨ ((p2 ∧ False) → (p5 → p2))))) ∨ p2) ∧ (p3 ∧ p5))) ∧ p2) ∧ ((p2 ∧ p4) ∨ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_193821959568003567393218860076 : ((p5 ∧ ((True → False) ∧ (((p5 ∨ p4) ∨ p2) ∨ p4))) → ((p4 ∧ (False → (False → (p4 ∨ ((True → p3) ∨ ((p1 ∧ p4) → True)))))) ∧ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h9 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h10 := h4 h9
        -- False on the left can always be used.
        apply False.elim h10
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- One of the premise coincides with the conclusion.
    exact h15
  -- Implications on the right can always be decomposed.
  intro h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- False on the left can always be used.
  apply False.elim h17
  -- Conjunctions on the left can always be decomposed.
  let h18 := h1.left
  let h19 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h20 := h19.left
  let h21 := h19.right
  -- Disjunctions on the left can always be decomposed.
  cases h21
  case inl h22 =>
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h25 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h26 := h20 h25
        -- False on the left can always be used.
        apply False.elim h26
      case inr h27 =>
        -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
        have h28 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h20, we can now drive its conclusion.
        let h29 := h20 h28
        -- False on the left can always be used.
        apply False.elim h29
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h30
  case inr h31 =>
    -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h20, we can now drive its conclusion.
    let h33 := h20 h32
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57102630172723871616936850746 : ((((True ∨ p3) ∧ p4) ∨ (((p5 ∨ p5) ∨ ((p2 ∧ (True ∨ (p2 ∨ p3))) → p1)) ∨ ((False ∨ (((False → p2) ∧ p1) ∧ p5)) ∧ p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147301711970302893134547960075 : (((((False ∨ ((True → p4) ∧ ((True ∨ p2) ∧ (((p2 ∧ p5) ∨ p5) ∨ p1)))) → (p3 ∨ p4)) → p5) ∨ p5) ∨ ((p4 → (p2 ∨ p3)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52534760652258989364068341044 : (((((p1 → p1) → ((True ∨ (False → (p3 ∧ (False ∧ False)))) → False)) ∨ True) ∨ ((((p5 → (p1 ∧ False)) → p2) → (False ∨ p2)) → p4)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358339280860404934682678478114 : (p5 → (True → ((((p4 → p3) ∨ (p2 ∧ (p5 → p4))) → ((((p1 → p2) ∨ True) → ((p2 ∧ (False → p2)) ∨ p4)) ∨ (p1 ∨ p5))) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_678777031134888132191810362647 : (((((p5 → True) → (p5 ∧ (p1 ∧ (((False ∧ (p3 ∨ p2)) ∧ p3) ∨ (p4 ∨ ((p3 → p4) ∨ p3)))))) ∨ (((p1 ∧ p4) ∨ False) → p4)) ∨ p3) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136038690061605007079708241496 : (((p4 ∧ (((p5 ∨ p3) ∨ ((p5 ∨ False) → p4)) → True)) → (((p5 → ((p2 ∨ p4) → p3)) ∧ p3) → (p1 ∧ p1))) ∨ ((False ∧ p4) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157563632225053466102318174194 : ((((((False ∧ False) ∧ p1) ∨ (True → (p4 ∨ False))) → ((False ∨ (p3 ∧ p1)) → True)) → (p2 ∨ p1)) ∨ (False → (p3 ∧ (p4 → (p3 ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184420287403520213010427453531 : ((((((p1 ∧ p5) ∨ p5) ∧ p5) ∧ (False → p5)) ∧ (p1 ∧ p1)) ∨ ((p2 → (False ∨ (((p2 ∨ p4) → (p2 → p2)) ∨ (p3 ∨ p2)))) ∨ False)) := by
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
theorem thm_5_vars_64420820545201335910187564176 : ((p1 ∨ ((True → (p2 ∨ ((((True → (p2 ∨ False)) → p1) ∨ ((((False ∨ p4) ∧ p5) ∧ p5) ∨ False)) ∨ ((True ∨ True) ∧ p1)))) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_865684144430213909583755908880 : (((((False ∧ (False ∧ (p1 ∧ p4))) ∨ ((True ∨ (False ∧ (p3 ∨ (True → (p1 ∨ (((False ∧ p1) → False) ∨ (p4 ∨ p3))))))) ∨ p2)) → p2) → p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((False ∧ (False ∧ (p1 ∧ p4))) ∨ ((True ∨ (False ∧ (p3 ∨ (True → (p1 ∨ (((False ∧ p1) → False) ∨ (p4 ∨ p3))))))) ∨ p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227783009381041601527487542276 : ((p1 ∧ (p2 → True)) ∨ (p5 → ((((p5 ∧ ((((False ∧ p2) ∧ p3) ∨ p1) ∨ (p3 → (p1 ∨ p2)))) → (False ∧ p1)) ∧ (p1 ∧ False)) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114377515025313960936692568137 : (((((p2 → (((p2 ∨ True) ∧ ((p1 ∨ p3) ∨ p4)) → p3)) ∧ ((True ∨ True) ∨ False)) → p2) ∨ ((p2 → (p2 ∨ p3)) ∨ False)) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59328702456616193926706449457 : (((p4 ∨ p4) ∨ ((p2 ∧ (p5 ∧ (p5 → ((((((p2 ∧ (True → p1)) ∨ p1) ∨ p5) ∧ False) ∧ p1) ∧ ((p1 → p2) ∧ p2))))) → p4)) ∨ p3) := by
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
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_972291022239345404969209656134 : ((((False ∨ True) → (((((p2 → p2) ∨ p2) → (p2 → p3)) → p4) ∧ (p3 ∧ ((((p5 ∧ p5) → (True → p4)) ∨ p2) ∧ (p5 ∨ p5))))) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156857803796717791917490165744 : (((((p5 ∨ (p3 ∨ ((p2 ∨ (True ∨ False)) ∨ (False → ((p3 → p5) ∧ True))))) ∨ p4) ∧ p2) ∨ False) ∨ ((p4 ∨ (True → True)) ∨ (p1 ∨ p2))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137379270295412468117117859643 : ((p3 ∧ (((False ∨ (p3 ∨ (False ∧ True))) ∨ (True → p2)) ∨ (p4 → ((p5 ∨ False) → (False ∧ (True ∧ (p5 ∧ p2))))))) ∨ (True ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731794723173683750832552572250 : ((((p3 → (p1 → p3)) → (p3 ∨ ((True ∧ ((p4 ∧ False) ∧ ((p3 ∧ ((p1 → p2) → (p2 → ((p2 ∧ p3) ∨ p4)))) ∨ p1))) ∧ p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_477245062022119089829695508678 : (((((p4 ∨ (((p2 ∧ (p4 ∧ p5)) ∧ p3) → p2)) ∧ p4) → ((True ∧ True) → ((True ∨ (p3 ∧ p5)) → (((p5 ∧ p3) ∧ p5) ∨ p4)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h14 := h2.left
    let h15 := h2.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h1.left
    let h17 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
    case inr h19 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h17
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142591870815604175879744904829 : ((False ∨ (((True ∨ ((((((True ∧ p5) → (True → p1)) ∧ True) ∧ (p3 ∨ p2)) ∧ p5) → p4)) ∧ p3) → (p1 ∧ p1))) → (True → (p4 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693153913331547259982333862772 : ((((p5 ∧ ((p4 → (p3 ∧ (p3 ∧ (p4 ∨ False)))) → ((p4 ∨ p3) ∧ True))) ∧ (p5 ∨ (((p5 ∧ p3) → p3) ∨ (True → (p2 ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251015577605523079698015975080 : ((p1 → p5) ∨ (((False ∧ False) ∨ (False ∧ (p5 ∨ (False ∧ p5)))) ∨ (((False ∧ ((p5 → p5) ∧ False)) ∨ ((p4 ∧ False) → False)) ∧ (True ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112429822431399786200254746619 : (((((((p5 ∧ ((p2 → p2) ∧ p1)) → (p3 → p4)) ∨ (((((p3 ∧ p1) ∧ True) ∨ p5) ∨ p4) ∧ p4)) ∧ True) ∨ True) → p2) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214396320410583010642605629792 : (((False → (p3 ∨ p3)) → p3) ∨ (p2 ∨ (((((True → p3) ∨ (p4 ∧ p1)) ∨ p2) ∨ ((False → p2) ∨ p1)) → (p4 ∨ ((p5 → p1) → True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h13
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136400161863804055036493244794 : (((p3 ∨ ((True ∨ p5) → False)) ∨ (((p5 → (((p5 ∨ p3) ∧ False) ∧ (p4 ∨ False))) ∧ (p2 → False)) → (p3 ∧ p4))) ∨ (False → (p3 ∧ p5))) := by
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
theorem thm_5_vars_763384581759065360103905185626 : (((p3 ∧ (True ∧ ((((p4 ∧ p2) ∨ (False → (p3 ∧ ((p5 ∧ (p5 → p2)) ∧ p1)))) ∧ ((p3 ∨ (False → p1)) ∨ (True ∨ False))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_203551560398463490252763069304 : ((p1 ∨ ((False ∨ (p1 → p5)) ∨ True)) ∧ (((p5 ∨ (((p1 → ((True ∨ ((p2 → True) ∧ True)) → (p2 ∨ p4))) ∨ False) ∧ True)) ∨ p3) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300084803419032883648260018378 : (False ∨ (((p1 ∧ ((p5 ∧ (p5 ∨ ((p1 ∨ (False ∨ (True ∧ p1))) ∨ ((p5 ∧ p3) ∨ p5)))) ∨ (p4 ∧ p4))) ∧ (p1 ∧ p2)) ∨ (p5 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60217145093956426332062618613 : (((True → p1) → ((p1 ∧ (((False → (True ∨ ((((p4 → p5) → False) ∨ (p4 → p3)) ∨ p4))) ∨ p4) ∧ (True → (p2 ∧ p2)))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150147007884052277959156705923 : ((p1 → ((p5 ∧ (p2 → (True → (((p2 ∨ (((True ∨ p3) ∨ (p1 ∧ True)) ∧ p4)) ∧ p4) ∨ p5)))) ∨ p1)) ∨ ((p2 ∧ (p3 → p4)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181436048511789007943966435818 : ((p3 ∨ ((p1 ∨ (((p3 ∧ p5) → p5) → ((p2 ∧ p5) ∨ True))) → p3)) → (p1 → ((((p3 ∧ True) ∨ p1) ∧ p3) ∨ ((p1 ∧ p3) → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 ∨ (((p3 ∧ p5) → p5) → ((p2 ∧ p5) ∨ True))) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208015796042694610592627336747 : ((((p3 ∨ True) → p2) ∨ (False ∨ p5)) → (((((p4 ∧ p3) ∨ p3) → p3) ∧ False) ∨ (((p5 ∧ p3) → ((False → p2) → p2)) → (p5 ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p3 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50139991512537363648550344243 : (((True → ((p2 ∨ ((p3 ∨ p1) ∨ p1)) ∧ (True ∧ ((((p1 ∧ p3) → (True ∧ False)) ∧ True) → False)))) ∧ (p3 ∨ ((False ∧ p5) ∨ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113521888379611354482832236645 : (((((p5 → (p4 ∧ p4)) ∨ (p4 ∧ (False → (p2 ∨ True)))) → ((((p1 ∧ (p4 ∨ False)) → p5) ∧ p5) ∧ p5)) ∨ (p5 ∨ p2)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350061983316224402724215575777 : (p4 → (((p1 ∨ ((((p3 → p1) ∨ True) ∧ (((p4 ∧ False) ∨ (p2 → False)) → (False ∧ (p2 ∨ (True → False))))) ∨ False)) ∧ (True ∧ p5)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774914338849808061971491374894 : (((False ∨ ((p2 → (p4 ∧ (p4 → p5))) → (p4 → (p4 → (p5 ∨ ((p1 → True) ∨ (p2 → (((True → p5) ∧ (False → p5)) → p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69101315076962130102858650280 : ((p5 → ((((((True ∨ p4) → (((p2 ∧ False) ∧ p5) ∨ False)) ∧ ((p3 ∨ ((False ∧ p5) ∧ p5)) → p3)) ∧ p1) ∨ p5) ∧ (p5 ∨ p4))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54435436489545624495510009700 : ((((p5 ∧ (p2 ∨ (p3 ∧ (p5 ∧ p5)))) ∨ False) ∨ ((p1 ∧ (p1 → True)) → (True ∨ ((((False → (p4 ∧ True)) ∨ p3) → p4) → p2)))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37457365684836715865758214683 : ((((((p1 → p1) ∨ (False ∨ ((False ∧ p5) ∨ (p5 → p2)))) ∧ ((((p2 → (True ∧ True)) → (p3 ∧ True)) ∨ p3) ∧ p4)) ∨ p5) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69487996495300444643911187175 : ((((((p3 → (p5 ∧ (((p3 ∧ p2) → p2) ∧ p1))) ∧ ((p5 → p4) ∨ (False → (p5 ∧ (False ∧ True))))) ∧ (p2 ∧ p4)) ∧ p2) ∧ p3) → p1) := by
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
  cases h9
  case inl h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h7.left
    let h12 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h13 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h14 := h8 h13
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- One of the premise coincides with the conclusion.
    exact h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h7.left
    let h19 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h20 : p3 := by
      -- One of the premise coincides with the conclusion.
      exact h3
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h21 := h8 h20
    -- We need to get the right conjuct of h21 based on <expert-advice>.
    let h22 := h21.right
    -- We need to get the right conjuct of h22 based on <expert-advice>.
    let h23 := h22.right
    -- One of the premise coincides with the conclusion.
    exact h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322420867838402902091376976885 : (p5 ∨ (((p1 → (True ∧ ((p1 ∧ (p3 → p3)) ∧ False))) ∧ (((p5 → p1) ∧ (p4 → ((p3 ∨ (False ∧ p3)) ∨ p5))) ∨ (p5 ∨ p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764750892892116585807652508271 : (((p4 ∧ ((p5 → ((p4 ∨ (p4 ∧ (((p1 → p4) ∧ ((p2 → True) → p1)) ∧ ((False ∨ (p5 ∧ p4)) ∧ p5)))) → (True → p2))) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110958033918376617840760392423 : (((((((p5 ∧ False) → True) ∧ ((p5 ∨ ((p1 ∨ p4) ∨ p1)) ∧ (False ∨ p1))) → ((False ∨ p3) ∨ p2)) ∨ (False ∨ True)) ∧ p4) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192264619027400460278740496914 : ((((p2 → (p5 → p4)) ∨ ((p1 ∨ p5) ∨ p4)) ∧ p4) → ((((p1 ∧ p2) → p1) ∧ (p4 → p2)) ∨ (True ∧ (((False ∧ p2) ∨ p4) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345500626578765413951769959392 : (p3 → ((((p2 ∧ p4) ∧ ((p2 ∧ (p3 ∧ p5)) ∨ (p1 ∧ (p3 ∧ (True ∨ (p1 ∧ True)))))) ∨ (((p1 ∨ p2) ∨ p2) ∧ (p2 → p3))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_958372917057484387496992685801 : ((((p4 → (p1 ∨ True)) → ((((p5 ∨ (False ∨ ((p3 ∨ p3) ∨ ((p2 ∨ p3) ∨ ((p5 ∧ (p1 → p2)) ∧ p5))))) ∧ p4) ∧ False) ∧ p3)) → p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 → (p1 ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310660260582728861008173109169 : (p2 ∨ (((p2 ∧ (False ∧ True)) ∨ p1) → ((p5 ∨ (((p3 → p4) → (p2 ∨ (p5 ∨ False))) ∨ True)) ∨ ((False → ((p2 ∧ p5) ∧ p5)) → False)))) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321658158655638878344257770418 : (p4 ∨ (p4 → ((((((False ∧ p2) ∧ (p5 ∨ p5)) ∨ (False ∨ p4)) ∨ p2) ∧ (((((p3 ∧ (p1 ∧ True)) ∨ p3) → p3) → False) ∨ p3)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171692048260703834114073103530 : (((True → (((False → (((p4 ∨ p4) ∧ p2) → (p4 ∧ False))) → p1) → p2)) ∨ p4) ∨ (((p5 ∨ p4) ∨ ((True ∨ True) → True)) ∨ (p3 ∧ p3))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119380057641770659283135677403 : ((p3 → (p1 → ((True ∧ (p4 → p3)) → ((p3 ∧ p2) ∧ (((True ∨ p3) ∧ ((p4 ∧ (True → p2)) ∧ True)) ∨ (p5 ∨ False)))))) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116977486855336471435675149594 : (((p4 ∧ p5) → ((p2 ∨ p3) ∨ (((p3 → (False ∨ True)) → ((((False ∧ False) ∧ p4) ∧ (p4 → True)) ∧ (False → False))) ∨ p3))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_744998307000659476638417975466 : ((((p4 ∧ p1) → (((p4 → ((((p3 ∧ (p4 ∧ p4)) ∨ (((True ∨ (True → False)) → False) → p4)) ∨ p2) ∧ (p2 → True))) → p3) ∨ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_783365973571365579311626751307 : (((p3 ∨ ((((p1 → p5) → (((False ∧ (p2 ∨ (p2 → True))) ∨ (p3 ∨ p5)) ∧ p3)) ∧ p1) ∨ ((p3 ∧ (p3 → (False ∧ p3))) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253804722777394273894028866386 : ((p1 ∧ p2) → ((((False ∨ p5) ∧ (p4 ∧ p3)) ∨ ((True ∧ False) → ((p2 → p5) → True))) ∧ (((True ∨ p2) ∧ (p3 ∨ (False ∨ p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204399016654046847139913170190 : (((p1 → ((p2 ∨ p2) ∨ p3)) ∧ p2) ∨ ((((((True ∨ (p4 ∧ (p5 → p3))) ∧ p4) ∧ p5) ∨ (p2 ∨ p2)) ∨ (True → p4)) ∨ (True ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197084682658882745764642992340 : (((p1 ∧ ((p1 ∨ (p3 → False)) ∨ p5)) ∨ p4) ∨ ((((p2 ∧ p1) → False) ∧ ((True ∧ (p4 ∧ ((p5 ∨ p2) → True))) ∧ p2)) ∨ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322418603795057067026447097757 : (p5 ∨ ((((p4 → ((p3 ∨ p1) ∨ (p4 ∨ False))) ∨ p4) ∧ ((p2 → (p4 ∧ ((p3 ∨ ((p1 → (p3 → p1)) ∨ False)) ∧ p3))) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654119583841252738781977209385 : (((((((((p2 → p4) ∨ (p3 ∨ ((((p4 ∧ p5) ∧ p3) → False) ∧ (p1 ∧ p4)))) ∨ p4) → (p4 ∧ p1)) ∧ p1) ∨ False) ∨ (p4 → p4)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_347681043331767132049895035495 : (p3 → ((p5 → ((p2 ∨ p2) → False)) → ((((p4 ∨ True) ∨ p1) → (p4 ∧ p5)) → (True → ((p5 → (p4 → p5)) ∧ ((p5 → p4) ∧ p4)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h8 : ((p4 ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h9 := h3 h8
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- One of the premise coincides with the conclusion.
  exact h10
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h11 : ((p4 ∨ True) ∨ p1) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h12 := h3 h11
  -- We need to get the left conjuct of h12 based on <expert-advice>.
  let h13 := h12.left
  -- One of the premise coincides with the conclusion.
  exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114651964259672787774167361969 : (((((p2 ∧ (False → (p3 ∧ p4))) ∧ (p2 ∨ p3)) ∧ ((p2 → (p1 → p2)) → True)) ∨ ((((p1 ∧ p4) ∨ p5) ∨ p4) ∧ False)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258783168598569085770931395610 : ((True → False) → ((p3 ∧ (((p4 ∨ ((True ∧ True) ∨ (p5 ∨ p5))) ∧ (p2 ∨ True)) → (p4 ∧ False))) ∧ (p3 → ((True ∧ False) ∧ (p5 ∧ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h14 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h15 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h16 := h1 h15
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h18 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h19 := h1 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h22 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h23 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h24 := h1 h23
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h26 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h27 := h1 h26
          -- False on the left can always be used.
          apply False.elim h27
      case inr h28 =>
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h29 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h30 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h31 := h1 h30
          -- False on the left can always be used.
          apply False.elim h31
        case inr h32 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h33 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h34 := h1 h33
          -- False on the left can always be used.
          apply False.elim h34
  -- Conjunctions on the left can always be decomposed.
  let h35 := h4.left
  let h36 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h37 =>
    -- Disjunctions on the left can always be decomposed.
    cases h36
    case inl h38 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h39 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h40 := h1 h39
      -- False on the left can always be used.
      apply False.elim h40
    case inr h41 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h43 := h1 h42
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- Disjunctions on the left can always be decomposed.
    cases h44
    case inl h45 =>
      -- Conjunctions on the left can always be decomposed.
      let h46 := h45.left
      let h47 := h45.right
      -- Disjunctions on the left can always be decomposed.
      cases h36
      case inl h48 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h49 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h50 := h1 h49
        -- False on the left can always be used.
        apply False.elim h50
      case inr h51 =>
        -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
        have h52 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h1, we can now drive its conclusion.
        let h53 := h1 h52
        -- False on the left can always be used.
        apply False.elim h53
    case inr h54 =>
      -- Disjunctions on the left can always be decomposed.
      cases h54
      case inl h55 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h56 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h57 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h58 := h1 h57
          -- False on the left can always be used.
          apply False.elim h58
        case inr h59 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h60 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h61 := h1 h60
          -- False on the left can always be used.
          apply False.elim h61
      case inr h62 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h63 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h64 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h65 := h1 h64
          -- False on the left can always be used.
          apply False.elim h65
        case inr h66 =>
          -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
          have h67 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h1, we can now drive its conclusion.
          let h68 := h1 h67
          -- False on the left can always be used.
          apply False.elim h68
  -- Implications on the right can always be decomposed.
  intro h69
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h70 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h71 := h1 h70
  -- False on the left can always be used.
  apply False.elim h71
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h72 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h73 := h1 h72
  -- False on the left can always be used.
  apply False.elim h73
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58632372194059372520635054606 : (((p1 → True) ∧ ((p5 ∨ (((p2 ∨ (p4 → p2)) → (p5 ∧ ((p5 → (p3 ∨ True)) ∨ p2))) ∧ p2)) ∨ ((True ∨ (p1 → False)) → True))) ∨ p3) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263009324054040077718507356747 : (True ∧ (((((p1 ∨ ((p4 ∧ True) → p5)) → p4) ∧ p5) → (p4 ∨ (p1 → ((((p2 → (p3 ∧ True)) → p3) ∧ p5) → False)))) ∧ (False → False))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p4 ∧ True) → p5)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h8 := h2 h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165588544793818081118871004636 : (((p1 → ((p4 → p2) → ((False ∧ p2) ∧ p2))) ∨ ((True ∧ p3) ∨ ((False → False) ∨ p1))) ∨ (p4 ∧ ((p1 → (p1 ∧ p3)) ∨ (p5 → p3)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_702290932406961594037846944642 : (((((p5 ∧ (True → ((False ∨ p3) → (p4 ∧ p1)))) ∧ True) ∨ ((p2 ∧ (p2 → False)) ∨ ((p4 → ((p1 ∧ (p2 ∨ p4)) ∨ p1)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261348006503853529688044711864 : ((p5 → False) → ((True ∧ p3) ∨ (((p1 → p3) ∧ ((((False ∨ p4) ∧ ((p3 → p4) → (p5 ∨ p1))) → ((p5 ∨ p3) ∨ False)) ∧ p5)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122242073372944456504216488133 : ((((p1 ∨ (True → p5)) ∧ ((((p3 → (((p2 ∨ True) ∨ True) ∨ p3)) ∨ ((p3 → True) ∨ False)) → p4) → False)) ∧ (p5 ∨ p2)) → (p4 → p1)) := by
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
    cases h4
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h9 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h11 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h12 : (((p3 → (((p2 ∨ True) ∨ True) ∨ p3)) ∨ ((p3 → True) ∨ False)) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h18 := h6 h12
      -- False on the left can always be used.
      apply False.elim h18
    case inr h19 =>
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h20 : (((p3 → (((p2 ∨ True) ∨ True) ∨ p3)) ∨ ((p3 → True) ∨ False)) → p4) := by
        -- Implications on the right can always be decomposed.
        intro h21
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- One of the premise coincides with the conclusion.
          exact h2
        case inr h23 =>
          -- Disjunctions on the left can always be decomposed.
          cases h23
          case inl h24 =>
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h25 =>
            -- False on the left can always be used.
            apply False.elim h25
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h26 := h6 h20
      -- False on the left can always be used.
      apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249553113208159915114369629751 : ((p5 ∨ p2) ∨ ((((True ∨ p3) ∨ (((p2 ∨ (False ∨ p1)) ∨ True) → False)) → ((p2 → False) ∧ False)) → (False ∨ (True → (p2 ∨ (p3 → p5)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∨ p3) ∨ (((p2 ∨ (False ∨ p1)) ∨ True) → False)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158418396962222376338464879829 : (((p3 ∧ p2) ∨ ((((((p4 → True) → p2) ∨ (p4 → p1)) → p2) ∧ (p5 → True)) ∧ (p5 ∧ p1))) ∨ ((p3 ∧ (False ∧ p5)) → (p3 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h4
  -- Conjunctions on the left can always be decomposed.
  let h6 := h1.left
  let h7 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338514137892834757535884972129 : (p1 → (((p1 ∧ p5) ∨ False) ∨ (p2 → ((p2 ∧ True) → (p3 ∨ (p1 ∧ ((p2 ∧ (((False → p4) → p3) ∨ (p3 → False))) ∨ (True ∧ p2)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636576745544790705955280268883 : (((((True ∨ ((True → ((((p4 ∨ True) → True) → (p5 ∧ True)) ∨ p1)) ∧ p1)) ∧ ((p5 ∨ p5) ∧ ((p5 ∧ (p3 ∧ p3)) → p1))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691340146305582332898957747416 : (((((p2 ∧ (False → p2)) ∨ (((p1 ∧ (((False → p2) ∨ p4) ∧ p4)) ∨ p5) → p1)) → (p5 ∧ ((p5 ∨ (p3 ∨ False)) → (p5 → p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174058512124325302675496573740 : (((p3 → (p3 → (((p2 → (p2 ∨ True)) ∧ (p4 ∨ (p5 ∧ p2))) ∨ p1))) → p4) → ((False ∧ (p2 ∧ ((p4 → p5) ∨ p1))) ∨ (p1 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148066888301724296526512209571 : (((p4 → (((p1 ∧ (p4 → (p4 → (p2 ∨ p2)))) ∨ p2) ∨ ((p3 ∨ p1) → (False ∧ p2)))) ∨ (True ∨ p2)) ∨ (True ∨ ((p3 → False) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199156190574246668273326397974 : ((((False ∧ p1) → ((p4 → p3) → True)) ∧ p5) → (((p3 → (((p1 ∨ (p4 ∧ p4)) ∧ True) ∧ p5)) → ((p5 ∧ p4) → p1)) ∨ (p4 ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_599995428967758459735199647526 : (((((False ∨ True) → ((((True → False) ∨ (p2 ∧ (p2 ∨ (((p2 ∨ False) ∨ p1) ∨ ((p5 → (p4 ∧ p4)) ∧ p3))))) ∧ True) → p5)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157481422691542531579167839494 : ((((((p1 ∧ (p3 ∨ (p4 ∧ p2))) ∨ (p4 → True)) → p2) ∧ ((p2 ∧ p3) ∨ p3)) ∨ (p4 ∨ False)) ∨ ((p4 ∧ p1) → ((p5 ∧ p5) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_159490087920286964604025362884 : (((((p4 ∨ p1) ∨ True) ∧ (p3 ∧ (p3 ∧ ((p3 → True) → ((p3 ∧ p5) ∧ (p1 ∧ False)))))) ∧ p3) → ((p2 ∨ ((p1 ∧ p4) ∨ p2)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h5.left
      let h9 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
      have h12 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h13
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h11, we can now drive its conclusion.
      let h14 := h11 h12
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h5.left
      let h19 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
      have h22 : (p3 → True) := by
        -- Implications on the right can always be decomposed.
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h21, we can now drive its conclusion.
      let h24 := h21 h22
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- False on the left can always be used.
      apply False.elim h26
  case inr h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h5.left
    let h29 := h5.right
    -- Conjunctions on the left can always be decomposed.
    let h30 := h29.left
    let h31 := h29.right
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : (p3 → True) := by
      -- Implications on the right can always be decomposed.
      intro h33
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h34 := h31 h32
    -- We need to get the right conjuct of h34 based on <expert-advice>.
    let h35 := h34.right
    -- We need to get the right conjuct of h35 based on <expert-advice>.
    let h36 := h35.right
    -- False on the left can always be used.
    apply False.elim h36
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158422617416306365977674827559 : (((p4 ∧ p3) ∨ ((((p1 ∨ (p5 ∨ p2)) ∧ False) ∨ True) ∨ (p1 ∧ (((p5 ∨ p5) → p3) ∧ p5)))) ∨ (((p4 → False) ∧ (p4 ∧ p1)) → p5)) := by
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
theorem thm_5_vars_342158346633791972878722119344 : (p2 → (((((p5 ∧ (((p1 ∨ p5) ∧ True) → p3)) ∧ p4) ∧ (True → p5)) ∨ ((False ∨ p1) ∨ (p1 ∨ p5))) ∨ (((p3 ∨ p3) → p2) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649939994872266260194909330804 : (((((p5 → ((p3 ∧ ((True ∨ (((p2 ∧ (p3 ∨ p5)) → p5) ∨ (p3 ∨ p3))) ∨ p1)) ∨ p3)) ∧ (p5 ∨ (False ∨ p2))) ∧ (True → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49046405135767539845984015885 : ((((p5 → (((p3 ∨ ((p1 ∨ p3) → p4)) ∧ p4) ∨ ((p4 ∧ (False ∨ False)) → (p3 ∧ (p5 ∨ p1))))) → p1) ∨ ((p5 ∧ False) → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_209202460507770376323667719900 : ((p4 ∨ ((True → False) → (True ∨ p5))) → (((((p1 ∧ p2) → p1) → ((p5 → (False ∧ (False ∧ True))) ∨ (p4 → (p4 ∨ p5)))) ∨ p1) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712368079075066269477172360488 : ((((((False ∧ False) ∧ False) ∧ (p5 ∨ p5)) ∨ (((p5 → (p3 ∧ (p3 → (p2 ∨ p4)))) ∨ p4) → ((((p3 ∨ p3) ∨ False) ∧ False) → True))) ∨ p2) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_151533530818189127281058180565 : (((False → ((p4 ∧ (p2 ∨ ((True ∧ False) → p4))) → (((False ∧ p2) → False) ∧ (p3 → p5)))) ∨ (True ∨ False)) → ((p5 ∨ (True ∨ False)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- False on the left can always be used.
      apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



