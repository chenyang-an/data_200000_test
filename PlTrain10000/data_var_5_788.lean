variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41172819755330512620044682327 : ((((((((True ∧ (p1 ∨ p2)) → p5) ∨ ((p5 → False) → (p5 → p4))) → ((True ∨ False) ∧ p5)) ∨ True) → (p5 → (p4 ∧ p4))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43842445068512867099512007462 : ((((((p1 ∨ ((p5 ∨ True) → (False ∨ p5))) ∨ (p1 ∨ ((False ∧ (True ∧ p4)) ∧ (p1 ∨ (False ∧ p3))))) → p1) ∧ (p2 ∨ p2)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234833476501765585109550189224 : ((p5 → (p2 ∨ p5)) → (False ∨ (p1 ∨ (p3 ∨ (((p2 → True) → True) ∧ (((p2 → (p5 → (p4 → p5))) ∧ (p4 ∧ p4)) ∨ (True ∨ p2))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246034471791479657977190503057 : ((p4 ∧ False) ∨ ((p1 ∧ (((p2 ∨ p5) ∨ p2) ∧ (p5 → (False → p5)))) ∨ ((p2 ∨ p3) ∨ ((False → ((p2 ∨ p5) ∧ (p2 → p4))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_47291495568662269837867615328 : ((((p2 → ((p2 ∧ p2) ∨ p5)) → (((p2 ∧ (p4 → (p1 ∨ p2))) ∧ (p3 ∨ p5)) → ((p5 → p5) ∧ (p3 → p1)))) ∨ (p1 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3248265010905939086719822634 : ((p5 ∨ p1) ∨ ((((p4 → p5) ∧ True) ∧ True) ∨ (((p1 ∨ (p3 → False)) ∧ (p3 → (False → (False ∨ p5)))) ∨ ((p1 ∨ False) → True)))) := by
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
theorem thm_5_vars_50741031053668902136023541755 : (((p1 ∧ ((True → (p5 ∧ p4)) → ((p1 → ((True ∨ True) → False)) ∨ ((p3 ∨ p3) → (p5 ∧ p3))))) → (p5 ∨ ((True → p4) ∨ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_40119303985974432294617979276 : (((((True ∨ ((p3 ∨ (p3 → p5)) ∨ ((p3 → (p3 ∨ ((p3 ∨ (p2 ∨ p1)) ∧ p1))) ∨ (p4 ∧ p3)))) → (p2 ∧ p5)) ∧ True) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56326208869214523224326622399 : ((((p4 → (p3 ∧ p1)) ∧ p3) → (p3 → (((p2 ∨ p3) ∧ (True → p5)) ∨ (((((p5 ∨ True) ∨ p5) → p2) ∧ (p3 ∧ p5)) → p2)))) ∨ p5) := by
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h10 : ((p5 ∨ True) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h11 := h6 h10
  -- One of the premise coincides with the conclusion.
  exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345533508961269105653747412282 : (p3 → (((((((p2 ∨ False) → p5) → p3) ∧ p2) ∨ p1) ∧ ((p1 ∧ False) ∨ (p1 ∨ ((p4 → ((p1 ∧ p5) ∧ True)) ∧ (p5 ∧ p1))))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213398859737628211894323490806 : (((p1 ∨ (False ∧ True)) ∧ p4) ∨ (((p5 ∨ (False ∨ (p4 ∨ ((True ∨ (True ∨ p2)) ∨ p3)))) → (p5 → (p1 ∧ p2))) ∨ (False → (p5 → True)))) := by
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
theorem thm_5_vars_41701736326449602137404731626 : ((((((p2 ∧ p4) → True) → (True → False)) → (p4 ∧ (((p4 ∧ (True ∧ (p4 → (p4 ∨ (p3 → p3))))) ∧ (p4 ∧ p3)) ∨ p3))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_995182859727173510017931486390 : (((p5 ∧ ((((p3 ∧ (True → p3)) → (p3 ∨ p2)) ∧ (p2 → (False → p2))) → (((((p4 ∧ p2) ∧ p3) ∧ p2) ∨ (False → p4)) → False))) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p3 ∧ (True → p3)) → (p3 ∨ p2)) ∧ (p2 → (False → p2))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h10 := h3 h4
  -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
  have h11 : ((((p4 ∧ p2) ∧ p3) ∧ p2) ∨ (False → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- False on the left can always be used.
    apply False.elim h12
  -- We have shown the premise of h10, we can now drive its conclusion.
  let h13 := h10 h11
  -- False on the left can always be used.
  apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42670626943078443087610010718 : (((p4 ∨ ((p2 ∧ True) → ((p4 → (((p4 ∧ (((p4 ∧ (p3 → ((True ∨ p5) ∨ False))) → p3) ∨ True)) ∧ p3) → p2)) → p4))) ∨ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225230215589989521216066705293 : (((p5 ∧ p3) ∧ False) ∨ ((((False → (p2 ∨ (p5 ∨ (True ∨ p4)))) ∧ ((((p1 → p5) ∧ False) ∧ p4) → (False ∨ (p5 → True)))) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49571342721545757496666177829 : (((((p5 → (p1 ∧ (p2 ∨ False))) ∧ ((p1 ∧ p4) ∨ (p2 ∨ (p2 → p3)))) ∧ (((p2 → False) ∧ p5) ∨ False)) → ((p4 → True) → p2)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h13 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h14 := h5 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- False on the left can always be used.
      apply False.elim h18
  case inr h19 =>
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h21 =>
        -- Conjunctions on the left can always be decomposed.
        let h22 := h21.left
        let h23 := h21.right
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h24 =>
        -- False on the left can always be used.
        apply False.elim h24
    case inr h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h26 =>
        -- Conjunctions on the left can always be decomposed.
        let h27 := h26.left
        let h28 := h26.right
        -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
        have h29 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h28
        -- We have shown the premise of h5, we can now drive its conclusion.
        let h30 := h5 h29
        -- We need to get the right conjuct of h30 based on <expert-advice>.
        let h31 := h30.right
        -- Disjunctions on the left can always be decomposed.
        cases h31
        case inl h32 =>
          -- One of the premise coincides with the conclusion.
          exact h32
        case inr h33 =>
          -- False on the left can always be used.
          apply False.elim h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252014766880878215363120401591 : ((p4 → False) ∨ (p4 → (p2 → ((((p1 ∨ p4) → False) ∧ (p1 → (False ∧ ((p1 → p1) → ((p2 ∧ False) ∧ p4))))) ∨ ((p4 ∨ p2) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179710000802008250906632379128 : ((((True ∨ ((p1 → (p3 → (p1 ∧ (p4 ∨ p4)))) → True)) ∨ False) ∧ True) → (True → ((((p4 → (p3 ∨ True)) → False) ∨ p1) ∨ (p1 ∨ True)))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64540276906124922149772666960 : ((p1 ∨ ((True → (False ∧ (p5 → (p1 → p2)))) ∧ ((True ∧ (p3 ∧ p4)) ∧ (p4 ∧ (p5 ∧ (((p3 ∧ p1) ∧ True) ∨ (p4 → p3))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205557776060175544520399102071 : (((p5 ∨ False) ∧ (True → (p2 ∨ p3))) ∨ (p1 ∨ (False → ((p3 ∨ (False ∨ (p1 ∧ (p4 → (((True → False) → (p5 → p1)) ∨ p1))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165672948794945867881080374802 : ((((((p4 → p1) ∧ p1) ∧ p1) ∧ p3) → (((p5 → p4) → (False ∧ (p5 → False))) ∨ True)) ∨ (False ∨ (p1 → (((p3 → p5) → p4) ∧ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167402143018353008307476917535 : ((((p2 → True) ∨ ((p5 → (p3 → ((((False ∧ p5) ∧ p1) ∨ p3) → p2))) ∧ False)) → False) → ((p3 ∨ False) ∧ ((p5 ∨ (p4 ∧ p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 → True) ∨ ((p5 → (p3 → ((((False ∧ p5) ∧ p1) ∨ p3) → p2))) ∧ False)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185056052182935529460127803317 : (((False ∧ p1) ∨ (((p1 ∧ (p2 → False)) ∧ (False ∨ True)) ∨ p4)) ∨ ((p3 ∧ False) ∨ ((p1 → ((p5 → p1) → (p1 ∧ p1))) ∨ (p5 → False)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137489702130546770586837474065 : ((p5 ∧ ((p1 → (((((((True ∧ (p4 ∨ p4)) ∧ False) ∧ p4) → p1) ∧ (p1 ∧ p2)) ∧ True) → (p4 ∧ p1))) ∨ p3)) ∨ ((False ∧ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690800698065458739693586437072 : ((((((p2 ∧ (False ∨ p5)) ∨ (True → (((p4 ∧ p4) ∨ False) ∨ (p1 → p1)))) → False) → (p1 ∨ (p1 → (((p4 → False) ∨ p4) → p4)))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p2 ∧ (False ∨ p5)) ∨ (True → (((p4 ∧ p4) ∨ False) ∨ (p1 → p1)))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301330746830318870762057581859 : (False ∨ (((True ∨ p3) ∧ (True ∨ p2)) ∧ ((p4 ∧ (((p5 ∨ (p4 → ((p2 ∨ p4) ∨ p5))) ∧ (p3 → ((p3 ∨ p1) ∨ p2))) → p5)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159287424720998938170511270060 : ((p4 → ((p1 ∧ p5) ∧ (p4 → (((False ∨ p5) ∧ ((p4 ∧ ((False ∧ p4) ∨ p5)) ∨ p3)) ∧ p3)))) ∨ ((True → (p3 → (p4 ∨ p3))) ∨ p4)) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4013808941206546937342441854 : (p1 ∨ (p2 → ((True ∧ (True → (True ∨ p3))) ∧ ((p4 ∨ (p1 ∧ (False → (False → p2)))) ∨ (((False ∨ (p1 ∨ p2)) ∨ True) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197289005446042818539323507415 : (((((p2 ∧ p4) ∨ p2) → (p5 ∧ p3)) → p4) ∨ (p5 → ((p5 ∨ ((True ∨ ((p3 → p5) ∨ p2)) → ((p1 ∧ True) → (True ∧ p3)))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53211190110805467014305989640 : ((((True → (((p1 ∧ False) ∧ p3) ∨ p4)) ∧ (p2 ∧ (p4 ∨ p3))) ∨ ((False → p5) → (p1 → (p3 → (True ∧ (p3 ∧ (p1 ∨ p1))))))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134650354799817583152893891753 : ((((p5 → ((((p4 → p1) ∨ (False ∧ p5)) ∨ (p3 ∧ p2)) ∨ p4)) ∨ (p1 ∨ (p2 ∧ ((p2 → p2) → p2)))) → p3) ∨ (True ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317877542998813894735280849460 : (p4 ∨ (((False → p3) → (p4 ∨ (((p4 ∧ (((p4 → p3) ∧ p5) → p3)) ∨ True) ∧ (((p3 ∨ False) ∧ ((p4 → p2) ∨ True)) → True)))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147058412972800704582815838341 : ((((True ∧ (((True ∨ p4) ∨ p2) → ((p3 ∧ p5) ∨ True))) → ((True → p2) ∨ (p5 ∧ (p1 ∨ p2)))) ∧ False) ∨ ((p1 ∧ p5) → (True ∨ p5))) := by
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
theorem thm_5_vars_310615617732298046660426671651 : (p2 ∨ (((p2 → (False ∧ False)) ∨ p4) ∨ ((((p3 ∨ p4) ∧ p2) → p4) ∨ (((p4 ∧ p5) ∧ (p1 ∧ p1)) → (((p5 → p3) → p3) ∨ p4))))) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h3.left
  let h7 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47944954718630838126864091605 : ((((p1 ∧ (((p1 ∧ (((p2 ∨ p2) ∧ (p5 → (False ∨ p2))) → p3)) ∧ p4) → (False → p3))) ∨ (p2 ∨ (p2 ∨ p1))) → (p3 ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46415566678160766458274147833 : ((((True → (False ∨ ((p3 ∨ (p5 → p4)) ∨ p1))) → (((True → p3) ∨ (True ∧ (p2 ∨ ((p5 ∨ p2) → True)))) ∨ True)) ∧ (p4 ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653679602774976914438824272247 : (((((((p3 → (((p4 ∧ ((p2 ∨ (p3 ∨ p3)) ∧ p3)) → (False → False)) ∧ (p2 ∨ p1))) ∧ (p5 → True)) → p3) ∧ p2) ∨ (p4 → p4)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_116094507845365494987186888754 : ((((False → p3) ∨ True) ∧ (p3 → (((((False ∧ p4) ∨ (((p4 ∨ False) ∧ p2) ∨ (True ∨ False))) ∨ p5) → (p3 ∧ False)) ∨ True))) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116545564005642360794385549659 : (((False ∨ p4) ∧ ((((p2 ∨ (p2 → (((p5 → p5) → p5) → p4))) ∨ p3) → (p3 ∨ (p4 ∧ (True ∨ p1)))) → (False ∨ p1))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327891146552232622103321987587 : (True → ((p3 ∨ ((p1 ∨ p4) → (((((p2 ∧ False) ∨ p1) ∧ p5) ∨ ((False → p5) ∧ p3)) ∧ ((p1 → (p1 ∨ p2)) → p5)))) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133807593798193170953776300395 : ((((p3 ∧ p5) ∧ (((p4 ∨ p5) ∧ (p4 ∧ p4)) ∨ (((p3 → (p3 ∨ (p3 ∧ False))) ∧ (p3 ∨ p1)) ∧ p5))) ∧ False) ∨ ((p2 ∧ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64729338697869049424602991987 : ((p1 ∨ (p5 → ((p5 → False) ∨ (False ∨ (p5 → (((((True ∨ p3) → p5) ∨ (((p2 ∨ p5) → p3) → (p3 → p2))) ∧ p1) ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49031321491004596944707571970 : (((((p4 ∨ True) ∧ ((p3 → p5) → (((p5 → (True ∨ p5)) → p3) → ((p5 ∧ (p3 → p5)) → p4)))) → False) ∨ ((False ∧ p2) → p4)) ∨ p2) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313975138764979114600226206776 : (p3 ∨ (((p4 ∨ ((False ∨ ((p3 → (p4 → (p1 ∨ p4))) → True)) → p5)) ∨ (p1 ∨ (((p4 → True) ∧ p5) → (True ∨ p5)))) ∨ (p4 ∧ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61885999155858321137517441541 : ((p2 ∧ ((((False ∧ ((p3 → (False ∧ p1)) → False)) ∧ ((False ∨ (True → (((False ∧ p1) ∨ p2) ∧ False))) ∧ p3)) ∨ p3) ∨ (True ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111950197514262719013696741141 : ((((p1 ∧ (p5 ∨ ((True ∨ (p5 ∨ p1)) → False))) ∧ (((False ∧ (False → ((p3 ∨ p1) → (p3 → True)))) → p2) ∧ p3)) ∨ True) ∨ (p1 ∨ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_317654435757263985651544893633 : (p4 ∨ (((((True → p4) ∧ (True ∨ (True → (((p2 → ((p4 ∨ p3) ∧ (p5 ∨ ((p2 ∨ True) ∧ False)))) → p5) ∧ False)))) ∧ p5) → p4) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  cases h5
  case inl h6 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265695893672513306689103917780 : (True ∧ (p3 ∨ ((((p5 ∧ (True → (p4 ∧ (p3 ∧ True)))) → False) ∧ ((p3 → (True → (False ∨ True))) → ((p4 ∧ (p3 → False)) ∨ p4))) ∨ True))) := by
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
theorem thm_5_vars_142409031838819312423066072758 : ((p4 ∧ (((True → True) → (p1 ∧ False)) ∨ (((p1 ∨ (False ∨ p1)) → ((((True → p3) ∧ p5) ∨ True) ∨ True)) → False))) → (p2 ∧ (True → True))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (True → True) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p1 ∨ (False ∨ p1)) → ((((True → p3) ∧ p5) ∨ True) ∨ True)) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- False on the left can always be used.
          apply False.elim h14
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h16 := h9 h10
    -- False on the left can always be used.
    apply False.elim h16
  -- Implications on the right can always be decomposed.
  intro h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138830433400638492626905211977 : (((p3 ∧ (((p4 → p4) → p3) → (((p3 ∨ (True ∨ p3)) → (p3 ∧ (p1 ∧ ((p1 → p4) ∨ p1)))) ∧ True))) ∧ p1) → ((True → p5) ∨ p3)) := by
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
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113685469175972943975162023578 : ((((((p3 ∧ (p1 ∨ p2)) ∨ (p3 → (((p2 ∨ (p5 ∨ False)) → ((p3 ∧ False) ∧ p3)) → p2))) ∨ p5) → p2) → (p4 ∨ p1)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247743917054176841886767721010 : ((p1 ∨ False) ∨ ((p5 ∨ True) ∧ ((p3 ∨ (p2 → (p5 ∧ ((p5 → True) ∨ (((p5 → p1) ∧ (p5 ∨ p1)) ∧ p5))))) ∨ ((p4 ∧ p3) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_111812552317171675939923917621 : (((((p1 ∧ p4) → (p5 ∧ (True → (True ∧ ((((True ∧ p2) ∧ (p5 ∧ (p2 ∧ p4))) ∨ True) ∨ p3))))) → (p4 ∧ True)) ∨ False) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42676939617052259135720429257 : (((p4 ∨ (p2 ∨ ((p5 → ((p2 ∨ p2) → ((p4 ∨ (True ∧ p3)) ∧ ((p2 ∨ (p2 ∧ (p1 ∧ p2))) → True)))) ∨ (p1 ∨ True)))) ∨ p1) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313250190235071464797254910711 : (p3 ∨ (((True ∨ p2) → ((((p2 → True) ∧ p2) ∧ (p5 ∧ ((p3 ∧ (p3 ∧ p1)) ∧ False))) ∨ ((p5 → p2) ∨ (True ∨ (p2 → p5))))) ∨ p3)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655799051058161931015631719589 : (((((False ∨ (((True ∧ (p4 ∧ (((p2 ∨ p1) ∨ p4) ∨ p3))) → (p2 ∧ (p3 ∨ p3))) → p1)) ∨ (True ∧ (p5 → p4))) ∨ (True ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200465378158773705741443943049 : (((p3 → p3) ∨ ((True → (p3 → p1)) ∨ p1)) → (((p5 ∧ p5) ∨ (((p3 ∨ ((((p1 ∧ False) ∧ p2) ∧ p5) ∧ p5)) → True) ∨ p5)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
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
theorem thm_5_vars_115132877368419427524392872403 : (((((False ∨ p5) ∨ p1) → ((p5 → (p1 ∨ (p3 → False))) ∨ False)) → (p1 ∧ (((p4 → p4) ∧ ((False → True) ∧ True)) ∨ p3))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309827292177641882511217383897 : (p2 ∨ (((p2 ∨ ((p2 ∨ (((p5 ∨ p4) ∨ (((p1 → p3) ∨ p2) ∧ (p5 → p1))) ∨ p3)) ∨ False)) ∧ p2) → (p3 → (p1 ∨ (p2 → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
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
        -- One of the premise coincides with the conclusion.
        exact h10
      case inr h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Disjunctions on the left can always be decomposed.
            cases h13
            case inl h14 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h15
              -- One of the premise coincides with the conclusion.
              exact h15
            case inr h16 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h17
              -- One of the premise coincides with the conclusion.
              exact h17
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h18.left
            let h20 := h18.right
            -- Disjunctions on the left can always be decomposed.
            cases h19
            case inl h21 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h22
              -- One of the premise coincides with the conclusion.
              exact h22
            case inr h23 =>
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- Implications on the right can always be decomposed.
              intro h24
              -- One of the premise coincides with the conclusion.
              exact h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- One of the premise coincides with the conclusion.
          exact h26
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134468298650389833497633510420 : ((((p1 ∧ (((((True → p5) ∨ p3) ∨ (p2 ∨ (((False ∨ p5) → p1) ∨ True))) → p3) → (p2 ∨ p2))) ∧ p2) → p4) ∨ (True ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174955272290546491252184318683 : ((True ∧ ((p2 ∨ (((((True ∨ (p1 ∨ p2)) → True) → p5) ∨ p4) ∨ False)) → False)) → ((((p3 ∧ (p5 ∨ p1)) ∨ True) → p4) ∨ (True ∨ p4))) := by
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
theorem thm_5_vars_39038591220452799376560171201 : ((((p5 → p1) ∧ (False ∨ ((True ∧ ((((p4 ∨ p2) ∧ p3) ∨ (p3 ∨ p3)) → ((True → p3) ∧ False))) → ((p2 ∨ p2) → p4)))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87431613591797901978817069075 : (((p4 ∨ (p5 ∧ (p3 ∧ (p5 → False)))) ∧ (True ∨ (((p3 ∨ p1) ∧ p5) ∨ ((p2 → (False ∨ (((p3 ∧ p1) → p1) ∨ p4))) → p2)))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h5 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h10 =>
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h11 =>
          -- One of the premise coincides with the conclusion.
          exact h4
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
  case inr h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h18 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h19 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h20 := h17 h19
      -- False on the left can always be used.
      apply False.elim h20
    case inr h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Disjunctions on the left can always be decomposed.
        cases h23
        case inl h25 =>
          -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
          have h26 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h17, we can now drive its conclusion.
          let h27 := h17 h26
          -- False on the left can always be used.
          apply False.elim h27
        case inr h28 =>
          -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
          have h29 : p5 := by
            -- One of the premise coincides with the conclusion.
            exact h24
          -- We have shown the premise of h17, we can now drive its conclusion.
          let h30 := h17 h29
          -- False on the left can always be used.
          apply False.elim h30
      case inr h31 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h32 : p5 := by
          -- One of the premise coincides with the conclusion.
          exact h14
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h33 := h17 h32
        -- False on the left can always be used.
        apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118605495551963556525112397280 : ((p4 ∨ (((False ∧ ((p4 ∧ p3) ∨ True)) ∧ (True → ((((p4 ∨ p2) ∧ p2) ∨ (False ∨ p2)) ∧ p3))) ∨ ((p4 ∧ False) → p1))) ∨ (p1 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_909635065463478837768208971250 : ((((p2 ∧ ((((p1 → p3) → ((((p2 ∨ p3) ∨ p5) → (p1 ∧ p5)) → p4)) → p1) → p4)) ∧ (True ∧ (((p5 ∨ p3) ∨ p2) → p1))) → p4) ∧ True) := by
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
  let h6 := h3.left
  let h7 := h3.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : ((p5 ∨ p3) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h10 : (((p1 → p3) → ((((p2 ∨ p3) ∨ p5) → (p1 ∧ p5)) → p4)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h12 := h5 h10
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58377675626910698754695484807 : (((p1 ∨ p3) ∧ ((((True ∨ (False ∨ ((((p3 ∨ p2) → ((False ∨ p1) ∨ p2)) ∨ p4) → p1))) ∨ p3) → (p2 → (p3 ∨ p5))) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43371201382120576871548869059 : (((((p5 ∨ (p3 ∧ (((p4 → p4) ∨ True) → ((p1 → (((True ∧ False) ∨ (p5 ∨ p2)) ∨ p3)) → p4)))) → (p1 ∨ p5)) ∨ p4) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314838577397484327552397865623 : (p3 ∨ (((p5 ∧ (p2 ∨ p1)) ∨ ((p5 ∧ True) ∧ ((False ∨ False) ∧ p3))) ∨ ((p2 ∨ ((p2 ∨ False) ∨ (p1 ∧ p1))) → ((False → p2) ∧ True)))) := by
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
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344772164025341407325946910308 : (p2 → (p4 → (((p5 ∨ (((p2 → (((True ∧ p5) → p4) → p4)) ∧ (p5 → False)) ∨ ((p5 → p5) → (p2 ∨ (p5 ∨ p5))))) → False) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592010525133731086291511401225 : (((((False ∧ ((True ∨ p5) ∧ ((((False ∨ p3) ∨ ((p1 → (p2 → (False ∨ (True ∧ p3)))) ∨ p3)) ∨ p3) ∨ p3))) ∨ (p4 ∨ True)) ∧ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_116200361828809858014054802677 : ((((p4 ∨ p2) ∧ p4) ∨ (p2 ∧ (p3 → ((p2 → p1) ∨ ((p3 ∨ p4) → (((((False → p4) ∨ True) ∨ p4) → p1) ∧ p3)))))) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184430367248528647773413251027 : (((((p3 ∧ False) ∧ False) ∨ ((False ∧ p4) ∨ p4)) ∧ (p1 → p4)) ∨ (True ∧ (p4 ∨ (True → (((p3 ∧ ((p5 ∧ False) ∧ p3)) → p1) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232211558747115839076880330986 : (((False → p5) → p3) → (True → ((True ∧ p5) ∨ ((p3 → (p4 → (p3 → p5))) ∨ (p4 ∨ ((p3 ∧ (p1 → (p2 ∧ p3))) → (p2 → True))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215383810414175969162944865138 : ((p2 ∧ (False ∧ (False ∧ p3))) ∨ (((((((p1 ∨ (p2 ∧ True)) → p5) → False) ∧ p2) → (p2 → p3)) ∨ p2) ∨ (False → ((True ∧ p4) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669200866121447178870141945609 : ((((((False → p1) → ((p4 ∨ ((p2 ∨ p2) ∨ (p5 ∧ (p4 ∧ p3)))) ∧ ((False → (p1 ∧ False)) ∧ False))) → False) ∨ ((True → p5) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_119516085212097082371089090332 : ((p5 → ((((((True → (p5 ∨ ((p2 ∧ p5) ∧ (False → (p3 → p3))))) ∨ False) ∨ (p2 ∧ (p1 → True))) ∧ True) ∧ False) ∨ False)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58199432037694911660030384645 : (((p4 ∧ True) ∧ ((((True → p1) ∧ (False ∨ p1)) ∨ (p1 → ((p5 ∧ ((p5 ∧ p5) ∧ p1)) ∨ p3))) → ((p3 → (p1 → p4)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42380202712422162217853663972 : (((p4 ∧ (((p1 ∨ (((p1 → False) ∨ True) ∨ (p2 ∨ (p3 ∧ p5)))) → (False ∧ (((p5 ∨ p1) ∧ p4) → False))) ∨ (p5 ∨ p2))) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172125028282212262296072158958 : ((((p2 → (p4 → ((p2 → p4) → p4))) ∧ (p5 → False)) ∧ ((p2 → p4) → True)) ∨ (((((p1 ∧ p3) ∧ True) ∧ (p3 → p2)) ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343214137461740901915238219304 : (p2 → (((p1 ∧ p2) → p3) → ((False ∨ ((p4 → True) ∧ p5)) ∨ (p1 ∨ (p1 → ((True ∧ (p5 ∨ True)) ∧ ((p1 → (p5 ∧ p1)) ∨ p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118647980515210399128525236660 : ((p4 ∨ (False ∧ ((p5 → p2) ∧ ((((p4 ∧ p1) ∨ (p4 ∧ p4)) → ((((p4 ∧ True) ∧ p3) ∨ (p1 → p3)) → False)) ∧ True)))) ∨ (True ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_614516049645768480349698181539 : (((((((p4 → (p2 ∨ (p3 ∧ p1))) ∨ ((p4 ∧ (p1 → p2)) ∧ (p2 → p3))) → (p4 ∨ p2)) ∧ (False ∧ ((True → p5) ∧ p3))) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_700245178110819934523335704817 : (((((True → p5) → ((p4 ∧ p5) ∧ (p1 ∧ ((True → p5) ∧ p1)))) → ((p3 → (p4 → (((p5 ∧ p3) ∨ True) ∨ (p4 → p1)))) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_4090468878523294144314896170 : (p3 ∨ (((((((((p5 ∧ (p4 → p4)) ∧ p5) → (p5 → p3)) ∧ p4) ∧ p1) ∨ False) ∨ ((p3 → p3) ∨ p1)) → (False ∨ p4)) → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p5 ∧ (p4 → p4)) ∧ p5) → (p5 → p3)) ∧ p4) ∧ p1) ∨ False) ∨ ((p3 → p3) ∨ p1)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115993389079163585121398228625 : (((((p4 ∨ p2) → p5) → p3) → ((((p2 → p3) ∨ False) ∨ True) → ((p3 ∧ ((p5 ∧ True) → p5)) → ((p2 ∨ p2) → p5)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323806604399234911430251546131 : (p5 ∨ ((p5 ∧ (((p1 → ((p3 ∨ p2) ∨ False)) ∨ (p3 ∨ (False → p5))) ∨ (False ∧ (p4 ∨ p4)))) ∨ ((p3 ∧ p4) ∨ (p1 ∨ (True ∨ p3))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199579357569458138662774602783 : ((((p3 ∨ ((False → p2) ∧ False)) ∨ p3) → True) → ((True → ((False ∧ p3) ∧ ((p4 → p4) ∨ (p5 → (p5 ∧ (p3 → p4)))))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_942122037153839144336564565882 : (((((False ∨ (p1 → p5)) ∧ p5) ∧ ((p4 ∧ ((True ∧ (p2 ∧ (p1 ∧ ((p1 ∨ p1) ∨ False)))) → ((p5 → (p5 ∧ p4)) ∨ p2))) ∧ True)) → p5) ∧ True) := by
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
    apply False.elim h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h8.left
    let h11 := h8.right
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219618059332028561655960206069 : ((False → ((True ∨ False) ∧ False)) → ((((True ∨ (((p5 ∧ p5) ∨ (True → ((p2 ∨ (False ∨ p4)) → p4))) ∧ (True ∨ False))) → False) ∧ p5) → False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : (True ∨ (((p5 ∧ p5) ∨ (True → ((p2 ∨ (False ∨ p4)) → p4))) ∧ (True ∨ False))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134011174828237964994048119382 : ((((p4 ∨ ((p1 ∨ (p4 ∧ ((p2 ∧ (True ∨ p4)) ∧ ((True ∧ (p4 ∨ (p2 ∨ p2))) → p1)))) ∧ p2)) ∧ p3) ∨ True) ∨ ((False ∨ p4) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602812974827056102880387349943 : ((((p1 ∨ ((((p5 → p2) → (p4 → (((p2 → p2) ∧ (p2 ∨ (((p3 → p3) ∧ p4) ∧ (p4 → p1)))) ∨ p2))) ∨ p4) ∧ p4)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213760379579451175061794282111 : ((((p5 → p2) → p5) ∨ p3) ∨ ((p1 ∨ (((p3 ∧ p2) → False) ∧ (p2 → False))) → (p1 ∨ (p1 → (True ∨ (((p4 ∨ p4) → True) → p3)))))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147121125668769009107565081035 : ((((p2 ∨ p5) ∨ ((p4 ∧ ((p2 → p5) ∧ p3)) ∧ (p4 ∨ (((False ∧ (False → p3)) ∨ p3) ∨ p5)))) ∧ p4) ∨ ((p3 ∧ (False ∨ False)) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327861981831166712885021395362 : (True → ((((p5 ∧ False) ∨ p5) → ((p2 → p1) → (False ∧ (p4 ∨ (((p4 ∨ p5) ∧ (False ∨ True)) ∨ (p1 ∧ (p4 ∨ p3))))))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_749674404068811596621389353791 : (((True ∧ (((p1 → (((p3 → (True ∨ (((True ∨ (p2 ∨ False)) ∧ p4) → p1))) ∨ (p1 → (p1 ∧ (p5 → p2)))) ∨ True)) → p5) ∨ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66313608512855922614902209704 : ((p5 ∨ (True ∧ ((((p5 ∨ p1) ∨ ((p3 → (p1 → (p1 ∧ True))) ∧ ((True ∧ False) → (p4 ∧ p5)))) ∧ (p1 → (p2 → False))) ∧ p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248588091217618145632479405078 : ((p3 ∨ False) ∨ ((((p3 ∧ True) ∨ (False ∧ p4)) ∧ p1) → ((p3 ∨ True) → (((p1 ∧ p3) → False) → (p5 → (p2 ∧ ((p4 ∨ p4) ∨ p2))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h1.left
    let h7 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : (p1 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h7
        -- One of the premise coincides with the conclusion.
        exact h9
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h12 := h3 h11
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- False on the left can always be used.
      apply False.elim h14
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h1.left
    let h18 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h22 : (p1 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h18
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h23 := h3 h22
      -- False on the left can always be used.
      apply False.elim h23
    case inr h24 =>
      -- Conjunctions on the left can always be decomposed.
      let h25 := h24.left
      let h26 := h24.right
      -- False on the left can always be used.
      apply False.elim h25
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h27 =>
    -- Conjunctions on the left can always be decomposed.
    let h28 := h1.left
    let h29 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h28
    case inl h30 =>
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h33 : (p1 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h29
        -- One of the premise coincides with the conclusion.
        exact h31
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h34 := h3 h33
      -- False on the left can always be used.
      apply False.elim h34
    case inr h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- False on the left can always be used.
      apply False.elim h36
  case inr h38 =>
    -- Conjunctions on the left can always be decomposed.
    let h39 := h1.left
    let h40 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h39
    case inl h41 =>
      -- Conjunctions on the left can always be decomposed.
      let h42 := h41.left
      let h43 := h41.right
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h44 : (p1 ∧ p3) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- One of the premise coincides with the conclusion.
        exact h40
        -- One of the premise coincides with the conclusion.
        exact h42
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h45 := h3 h44
      -- False on the left can always be used.
      apply False.elim h45
    case inr h46 =>
      -- Conjunctions on the left can always be decomposed.
      let h47 := h46.left
      let h48 := h46.right
      -- False on the left can always be used.
      apply False.elim h47



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_487593859176107508719623955457 : (((((p1 ∧ (p4 ∨ (p5 → p4))) → p1) → ((((p1 ∨ (p3 ∧ p4)) ∨ ((False ∧ (p3 → (True ∨ (p2 → False)))) ∧ p2)) ∨ p1) ∨ True)) ∧ True) ∧ True) := by
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
theorem thm_5_vars_184162017706590857317312946675 : (((p4 ∨ (p4 ∨ ((((True → p2) ∧ p5) ∧ p3) → False))) ∨ p5) ∨ (p1 ∨ (True ∨ (False → (p1 ∧ ((p5 ∧ p1) → (True ∨ (p5 ∨ True)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357314747053599793254202883232 : (p5 → ((p4 ∨ p2) ∨ (True → ((p4 ∧ ((p1 ∨ (p4 ∧ p1)) ∨ (((p1 ∨ p3) ∨ True) ∨ p2))) → ((p1 ∨ (True ∨ (True ∨ p3))) ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



