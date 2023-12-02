variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157392069727139908523061980075 : (((((((p1 ∧ ((((False → p5) ∧ p3) → p3) → p3)) → p1) ∨ p2) ∨ p2) → p3) ∧ (True ∨ p1)) ∨ (True ∨ (False ∨ ((p4 ∨ p2) ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745499069995424045048347426869 : ((((True ∨ True) → (p1 ∨ ((((False → (p2 ∨ ((False ∧ (p1 ∧ (p2 → p3))) ∨ False))) → ((p1 → (p2 ∧ p3)) ∧ False)) → p1) ∨ p5))) ∨ p3) ∧ True) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → (p2 ∨ ((False ∧ (p1 ∧ (p2 → p3))) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- False on the left can always be used.
      apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : (False → (p2 ∨ ((False ∧ (p1 ∧ (p2 → p3))) ∨ False))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- False on the left can always be used.
      apply False.elim h11
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- False on the left can always be used.
    apply False.elim h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_252614835166592764731883340897 : ((p5 → p3) ∨ (p2 ∨ (p2 → (((p5 → p4) ∧ ((((p5 → True) ∨ p3) ∧ p4) ∨ p4)) → (p1 → ((p2 ∨ False) ∧ ((p5 ∧ False) ∨ True))))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h10 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
  case inr h11 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Conjunctions on the left can always be decomposed.
  let h12 := h2.left
  let h13 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h13
  case inl h14 =>
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h18 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h19 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261147806991877894614096464854 : ((p4 → p4) → ((((p2 ∧ (((p5 ∧ p5) ∨ False) → (p2 ∧ (p1 → (p2 ∧ p2))))) ∨ (p5 ∧ p1)) ∧ (True ∧ p2)) ∨ ((p2 ∧ False) → p1))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_616526013830629129612960929788 : (((((p3 → (p4 → (True → ((False ∧ (p3 ∨ p5)) → (p5 ∨ False))))) → ((True → (p2 ∧ p1)) ∨ ((p2 → True) → (False ∨ p4)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_215280765493928560032839985801 : ((False ∧ (p4 → (p5 ∨ False))) ∨ ((p4 ∨ p4) ∨ ((p3 ∨ (p3 ∧ False)) ∨ (p5 → (((True ∧ (p4 ∨ True)) ∧ (False ∧ (True → True))) → p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- False on the left can always be used.
    apply False.elim h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h4.left
    let h12 := h4.right
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233746836615109617139813397823 : ((p3 ∨ (p5 ∧ p4)) → ((((p2 ∨ (((p5 → (p4 ∧ (p2 → (p2 ∨ p1)))) ∨ p2) → ((p2 → p5) ∨ p5))) ∨ p3) ∨ (p2 → True)) ∨ p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313998218362401673270970031218 : (p3 ∨ (((p4 ∧ p5) ∨ ((((p4 ∧ ((False → True) ∧ True)) ∨ (p1 ∧ (((True ∧ (p2 ∨ p1)) ∧ p4) → p3))) ∨ p2) ∧ True)) ∨ (p4 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139062391566446604646483250780 : ((((p4 → ((False ∨ (((p3 ∧ False) → p1) → p2)) ∨ ((p3 ∨ p1) ∧ ((p3 ∨ (p3 → p3)) ∧ p5)))) → p4) ∨ p4) → ((p1 ∧ p4) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254472987371552298263895411750 : ((p3 ∧ True) → ((((p3 → ((p2 ∨ (False ∨ p1)) ∧ p2)) → ((False ∨ p5) ∧ p2)) ∧ False) ∨ (p4 ∨ (p2 ∨ (p3 → (p4 ∨ (p5 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753501680249613116224764521258 : (((False ∧ (((p4 → ((p5 ∨ (False ∨ ((p2 → False) ∨ p4))) → p5)) ∧ ((p5 ∨ (p5 ∨ p5)) ∨ p4)) ∧ (p5 ∧ ((p2 ∧ False) ∨ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149154864988965262244479888219 : (((p1 ∨ p4) ∧ (False ∨ ((False ∨ p1) ∨ (((p5 ∧ False) → p5) ∨ ((p4 ∨ ((p5 ∧ p4) ∧ False)) ∨ False))))) ∨ (True ∧ ((p5 ∧ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_899847824094875207689449545751 : (((((True → (p4 ∧ ((True ∨ (True ∧ False)) ∧ False))) → (False ∨ (((p1 ∧ ((p5 ∨ p3) ∧ p5)) ∧ p5) ∨ p3))) → ((False ∧ p4) ∧ False)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True → (p4 ∧ ((True ∨ (True ∧ False)) ∧ False))) → (False ∨ (((p1 ∧ ((p5 ∨ p3) ∧ p5)) ∧ p5) ∨ p3))) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- False on the left can always be used.
  apply False.elim h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53432022579733287947535027719 : ((((p2 ∧ ((False → p1) → p5)) ∨ ((True → False) ∧ (p3 ∧ p3))) → (((((p5 → p1) → p5) → p3) ∧ p2) ∧ (p5 ∧ (p5 → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41503233741629139829874534495 : ((((True ∧ (((p1 ∧ p3) → (p5 ∨ p4)) ∨ ((p1 ∨ p4) ∨ p2))) → ((((False ∨ p5) ∧ False) ∧ p5) ∧ (False → (False → False)))) ∨ True) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58060932225669873586627346456 : (((False ∧ p2) ∧ (p5 ∧ ((((p2 ∧ True) → ((False ∧ p3) ∧ ((False ∧ p3) ∨ (p5 ∧ (p5 ∨ (p2 ∧ False)))))) ∧ (p4 → True)) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_640999439327560062649971477665 : (((((p2 ∧ p2) ∨ ((p1 ∨ (p4 ∨ ((p2 ∨ p5) → ((True → p2) ∨ p2)))) ∧ ((((p5 → p1) → (p5 ∧ p5)) ∧ True) ∧ True))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56950069299174327057796698908 : (((p1 ∨ (False → True)) ∧ ((p5 → True) ∧ (p3 ∧ (p3 ∧ (((p2 → ((True → p4) → p5)) → ((p3 ∨ True) → (True → p2))) ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309339999208713816122016767677 : (p2 ∨ ((((p2 ∧ ((p5 ∨ (((p3 ∨ False) → True) ∧ p2)) ∧ (p1 ∨ (p2 → (p4 → p5))))) ∨ p4) ∨ (p5 → (p3 → p1))) ∨ (True ∧ True))) := by
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
theorem thm_5_vars_914096170098169038073785809705 : (((((((((p2 → p3) ∨ (p4 ∨ p2)) ∧ p3) ∧ (p2 ∧ (p4 ∧ p1))) → p5) → False) ∧ (True ∧ (p5 ∧ ((p1 ∨ (p5 ∨ p2)) → p5)))) → p2) ∧ True) := by
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
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (((((p2 → p3) ∨ (p4 ∨ p2)) ∧ p3) ∧ (p2 ∧ (p4 ∧ p1))) → p5) := by
    -- Implications on the right can always be decomposed.
    intro h9
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h12 := h10.left
    let h13 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h11.left
      let h16 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Conjunctions on the left can always be decomposed.
        let h21 := h11.left
        let h22 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h25 =>
        -- Conjunctions on the left can always be decomposed.
        let h26 := h11.left
        let h27 := h11.right
        -- Conjunctions on the left can always be decomposed.
        let h28 := h27.left
        let h29 := h27.right
        -- One of the premise coincides with the conclusion.
        exact h6
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h30 := h2 h8
  -- False on the left can always be used.
  apply False.elim h30
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_790153663362938706816040939701 : (((p5 ∨ ((p4 → p5) → (p1 → ((p1 → ((p2 → (((p2 → p1) ∨ (p4 ∨ True)) → p5)) → (p5 ∧ p2))) ∧ ((p2 ∨ p3) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98934188547863900903046019744 : ((True → ((((p2 → (p4 → (p5 ∨ (p3 ∨ ((((p3 → (False ∧ False)) ∨ False) ∨ p1) ∨ (p2 ∨ True)))))) ∨ False) ∨ p2) → (False ∧ p3))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p2 → (p4 → (p5 ∨ (p3 ∨ ((((p3 → (False ∧ False)) ∨ False) ∨ p1) ∨ (p2 ∨ True)))))) ∨ False) ∨ p2) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h7 := h3 h4
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- False on the left can always be used.
  apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171834836145272957208920749534 : ((((p2 ∨ (p3 ∨ p2)) ∨ ((p5 → p5) ∧ ((p4 ∧ (False ∨ p5)) → False))) → False) ∨ (p5 → (p5 → ((((p5 ∨ False) ∨ p1) ∨ p4) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137005318649896110090316996503 : (((False ∨ p5) → (((False ∨ (((((p2 ∨ p5) ∧ (p1 ∧ False)) ∧ True) ∨ p4) ∨ (p5 ∧ (p2 ∨ p2)))) ∧ p3) ∨ True)) ∨ (True → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257497682912469487574431910591 : ((p3 ∨ False) → ((True → (p3 ∧ ((p3 ∧ (((True ∧ (p4 ∧ (True ∧ (p1 ∨ p5)))) ∨ (True → (p4 ∨ p4))) ∨ (p5 ∧ p3))) ∧ False))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41922168438086408190642643337 : ((((p3 ∧ (False ∨ p4)) → (((p2 ∨ p4) ∧ (p5 → (((((p2 ∧ p2) → p3) → p4) → p2) ∨ p3))) → ((p5 ∧ p1) ∧ p2))) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178344872422981024577963337599 : ((((p5 → p5) → ((((False ∧ False) → p3) ∨ False) → p1)) ∨ (False → p1)) ∨ ((p3 → p4) ∧ (((p2 ∨ False) ∧ p2) → ((p2 ∨ p3) → p1)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158886109051681665828419662564 : ((False ∨ (p5 ∨ ((p2 → ((True ∧ (False ∧ False)) ∧ (((p2 → (p5 → p5)) → p2) → p3))) ∨ p1))) ∨ (p3 ∨ (((p3 ∨ p3) ∨ p5) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241277036490150322863031486131 : ((False → True) ∧ ((p4 ∨ (((p4 ∧ ((p1 ∨ p1) ∨ (p4 → (p5 ∧ (p4 ∧ False))))) ∧ (((p5 → (False → p4)) → p3) → p5)) ∨ p4)) ∨ True)) := by
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
theorem thm_5_vars_685754314186226243581311230381 : ((((((p3 ∨ ((((p2 ∧ p5) ∧ p5) ∨ (((p1 ∧ True) → p2) → p4)) ∧ True)) ∧ True) → p4) → ((False → p2) → (p1 ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49140565842109913195790534842 : ((((((False ∨ (p2 ∧ (p2 → p2))) ∧ p1) ∨ (True → p4)) ∨ (p4 ∧ (p2 → ((True ∨ (True → True)) → p1)))) ∨ ((p3 → p3) ∨ p5)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50409759751443322321147934362 : (((False ∧ ((True → False) ∨ ((p5 → ((False → (p5 ∧ p4)) → p5)) ∨ (p3 ∧ (True ∨ (p3 ∨ p1)))))) ∨ (((p1 ∨ False) ∧ p2) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18125545970674818553386448926 : (((p4 → ((((((p4 ∨ True) → False) ∨ ((p1 ∨ p4) ∨ True)) → ((p5 ∨ p4) ∨ p3)) ∧ p4) ∧ False)) ∨ ((p3 → True) ∨ (p1 ∨ p4))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148024568801986235222495696848 : (((((False ∨ (p1 ∧ (False ∧ p5))) ∨ p5) → (p1 ∨ (p5 ∧ (((False ∧ p3) → p2) ∧ p3)))) ∨ (False ∧ p2)) ∨ (((p3 ∧ p5) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204584872413058662268874319486 : ((((p2 ∧ p2) ∨ (p4 ∨ False)) ∨ False) ∨ ((True ∧ False) → (p4 ∨ ((False ∧ ((p1 ∨ p2) → ((p3 ∧ p2) ∨ p5))) ∨ ((False ∨ p2) ∨ p2))))) := by
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
theorem thm_5_vars_65324999268705943373908111377 : ((p3 ∨ ((p1 ∨ ((((False ∧ (p5 ∨ True)) ∧ (p4 ∧ p1)) ∨ ((p2 → (False ∨ (p4 ∧ p1))) → p3)) ∧ p2)) → (p3 ∧ (p2 ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187727552814873842592533792957 : ((p1 → ((p2 → ((False ∧ p1) ∨ p5)) ∨ ((True → p4) ∨ p3))) → ((p4 → ((p1 ∧ True) ∨ p3)) ∨ ((True ∧ p2) ∨ (p1 → (p1 ∧ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160679472285603099534291531641 : ((((True ∨ (((p3 ∨ p3) ∧ p2) → p1)) → p2) ∧ (False ∨ (p3 ∨ ((p1 ∨ (p5 → True)) ∨ p3)))) → (((p4 → False) ∧ p1) ∨ (True ∨ p2))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736259343241237215263011005067 : ((((False → p3) ∧ ((((((True ∧ ((False → p1) ∨ True)) → ((p2 ∨ p1) ∨ False)) ∧ ((p1 ∧ p5) ∧ (p3 ∨ p4))) ∨ p4) ∨ p2) ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209207674121921040060960850907 : ((p4 ∨ (p3 ∧ (p1 ∨ (p1 ∨ True)))) → ((p3 ∧ (False ∨ True)) → ((((p5 → False) → (False ∧ (p5 ∨ (p4 → (True ∧ p2))))) ∨ p5) ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615475561932124284396824323862 : ((((((p4 ∧ ((p1 → (p4 → (p3 ∨ (p2 ∨ ((p1 → False) → p2))))) → False)) ∨ False) → (False ∧ ((p1 ∨ (p4 ∧ p1)) ∨ p2))) ∨ False) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (p1 → (p4 → (p3 ∨ (p2 ∨ ((p1 → False) → p2))))) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
      have h9 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h6
      -- We have shown the premise of h8, we can now drive its conclusion.
      let h10 := h8 h9
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h11 := h4 h5
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h13.left
    let h15 := h13.right
    -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
    have h16 : (p1 → (p4 → (p3 ∨ (p2 ∨ ((p1 → False) → p2))))) := by
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h19
      -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
      have h20 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h17
      -- We have shown the premise of h19, we can now drive its conclusion.
      let h21 := h19 h20
      -- False on the left can always be used.
      apply False.elim h21
    -- We have shown the premise of h15, we can now drive its conclusion.
    let h22 := h15 h16
    -- False on the left can always be used.
    apply False.elim h22
  case inr h23 =>
    -- False on the left can always be used.
    apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42598713961343840402461647103 : (((p2 ∨ (p3 ∨ (((((p5 → (True ∨ ((((p5 ∧ p3) ∨ (p2 → p5)) → p3) ∨ p5))) ∧ p4) ∧ False) ∨ p1) ∧ (False ∨ p5)))) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208638654211807157259137661208 : ((True ∧ ((p5 ∨ p5) ∨ (False ∨ True))) → ((p1 → ((p1 ∧ (p4 ∨ p4)) ∧ p4)) → ((True → (p1 ∧ p5)) → ((p1 ∨ (p3 ∨ p5)) ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h12 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h12
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609267161248313097472243279608 : ((((((p1 ∧ (p1 ∨ True)) → (p1 → (p2 ∨ ((p5 ∨ p4) ∨ (p4 → ((True → ((p1 → (p5 ∨ p4)) ∨ p2)) → p1)))))) ∨ p1) ∨ p4) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- One of the premise coincides with the conclusion.
    exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219348160187858606874644293710 : ((p2 ∨ (p4 → (p5 → p1))) → ((p4 ∨ ((p2 → (p2 → ((p1 → ((p4 ∨ p2) ∧ ((p4 → (p3 → p3)) → p4))) ∧ p1))) → p2)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633740514235469926859617277535 : (((((p3 ∨ (((((p1 → (p2 ∨ p2)) ∧ (p4 ∨ (p4 ∨ False))) ∧ (True ∧ (p1 ∧ (p1 → p2)))) ∧ p2) → p5)) ∨ (p3 → p1)) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98878288490839164008899044677 : ((True → (((False ∨ ((p2 ∧ p4) ∧ ((p3 → (p3 → ((True ∨ (p5 ∧ (p3 ∨ (p3 → (p5 → p5))))) → p5))) → p2))) ∨ True) → False)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∨ ((p2 ∧ p4) ∧ ((p3 → (p3 → ((True ∨ (p5 ∧ (p3 ∨ (p3 → (p5 → p5))))) → p5))) → p2))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62156297064897024944638928517 : ((p2 ∧ (p1 → ((p5 ∨ True) → (((p1 ∧ (p3 → p4)) → p3) ∨ (((p5 ∧ p3) → (p1 ∨ (True ∨ p4))) ∨ ((p1 ∨ p1) ∨ p5)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_199089311437559138573989148939 : ((((True → (p4 ∧ (True ∨ p3))) → p3) ∧ True) → (((False ∨ p3) ∨ ((True ∧ p1) → True)) → (True → (((False → False) → p5) ∨ (p3 → p3))))) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h1.left
      let h8 := h1.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_684533563160767491797907333766 : (((((p3 → (p4 ∧ ((p2 ∧ p5) ∧ p5))) → (((True → False) ∧ (p5 ∧ p4)) ∧ (False → p4))) ∨ (True → (((p2 ∧ p3) ∨ True) ∨ p2))) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233387762087743663810157960597 : ((False ∨ (p4 ∧ p5)) → (((((p1 → p4) ∧ (False → (((((p2 ∧ (p1 ∧ p4)) ∨ p2) ∧ p1) ∨ True) → p5))) ∧ p4) → (False ∧ p5)) ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209419843857610786841329516140 : ((p2 → ((p1 ∨ (p2 → p2)) ∨ p3)) → (((p5 → p2) ∨ True) ∧ (True ∨ (True ∨ (((p1 ∨ True) ∧ (((True ∧ p3) ∨ p1) ∨ p5)) ∧ p1))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225220585555856859654788297937 : (((p5 ∧ p1) ∧ p2) ∨ (((((p5 ∨ p5) ∧ ((((p4 ∨ False) ∧ p2) → (p4 ∨ p3)) ∧ (False ∧ False))) ∨ p3) ∧ ((p5 ∨ p3) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_123706312065686781541648585049 : ((((((p3 ∧ (p1 → p5)) → (p3 ∧ (p4 ∨ p5))) ∨ (p5 → p2)) ∨ p5) ∧ ((p1 ∧ (p1 → (p3 → p5))) ∧ (p4 ∨ p1))) → (p3 ∨ p1)) := by
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
      let h8 := h6.left
      let h9 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h3.left
      let h14 := h3.right
      -- Conjunctions on the left can always be decomposed.
      let h15 := h13.left
      let h16 := h13.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
  case inr h19 =>
    -- Conjunctions on the left can always be decomposed.
    let h20 := h3.left
    let h21 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h21
    case inl h24 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h22
    case inr h25 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336669832676715027096027264077 : (p1 → (((((((p1 → p5) ∨ p2) ∨ (((p3 → (p2 ∨ p4)) ∨ p1) ∧ (p2 ∧ p5))) ∨ p4) ∨ p1) → ((True ∧ p3) ∧ (p1 → p2))) → p2)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (((((p1 → p5) ∨ p2) ∨ (((p3 → (p2 ∨ p4)) ∨ p1) ∧ (p2 ∧ p5))) ∨ p4) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_757776640431407601878050069340 : (((p1 ∧ (False ∨ (p2 → (p4 ∧ ((((((False → p5) ∨ p3) ∧ p2) → (False → p5)) ∧ (p2 ∨ (True ∨ (False ∨ (p4 → p4))))) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190281658397067884509271663036 : ((((p2 → (((p1 ∧ p5) → False) ∧ p1)) ∨ p2) ∨ p4) ∨ (p4 → ((True ∧ False) ∨ (p4 ∨ (((p1 ∨ (p5 → p1)) ∧ (p1 ∧ p1)) ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354601065913269133818457555370 : (p5 → (((((((p1 → (((False ∧ p4) ∧ (p5 ∧ (True ∨ ((p4 ∨ (True ∧ p3)) → True)))) ∧ False)) ∧ False) ∧ p3) ∨ p4) ∨ p1) ∨ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161786718643416691886885917530 : ((p4 ∨ (p5 → (p5 ∧ (p1 ∨ (((p1 ∨ ((True ∨ True) ∧ p5)) → p1) ∧ ((p5 → p2) → p4)))))) → ((True → False) → ((True → p5) → p2))) := by
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
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1975898382956278450099232654 : ((p1 ∨ (True → ((p2 ∧ ((p4 ∨ p2) ∨ (p2 ∧ ((p4 ∧ (p5 ∧ p4)) → p2)))) ∨ (False → p2)))) ∨ ((p4 ∨ True) → (p3 ∨ p4))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111911724238468906851416693350 : ((((p3 ∨ ((p2 ∧ ((((p4 ∨ True) → p5) ∨ p2) ∧ p4)) ∨ True)) ∧ (((p1 ∨ (p1 → False)) → p2) → (p2 ∨ True))) ∨ p1) ∨ (p1 → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350922821695348228296883934672 : (p4 → (((p5 ∧ ((p2 → (p4 → (((p5 → False) ∧ p4) → (p4 → False)))) ∧ (p1 ∧ ((p4 ∧ p5) → (True ∨ p3))))) ∨ p1) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219975474519060452661461938344 : ((p5 → ((p1 → False) → p1)) → (((p1 ∧ (((p3 ∨ (p1 ∨ (True ∧ True))) → (p5 ∨ ((True ∧ p2) ∨ p1))) → (p2 ∧ True))) ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_619154123721571498394770192701 : (((((p2 ∨ (True ∧ p1)) ∨ ((p3 → p5) → ((p2 ∧ (p2 → False)) → ((False ∨ ((p1 → p4) ∧ ((False ∧ p4) ∨ p2))) ∨ p2)))) ∨ p4) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135114133333720158113680830600 : ((((p3 ∨ p5) ∧ (((p1 ∨ p3) → ((((True ∧ True) → (False ∨ p4)) ∧ p4) ∧ (False ∨ p2))) → p3)) ∨ (p5 → p5)) ∨ ((p4 → p3) ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623512633209872311995343406845 : ((((False ∨ (((p3 ∧ p2) ∨ (p3 ∧ (p2 ∨ p4))) ∧ ((p1 ∨ ((p5 → p4) ∧ ((p5 → p5) ∨ (True ∧ p2)))) ∨ (False ∨ False)))) ∨ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157073108053350614307367510633 : (((p1 ∨ (((p3 → ((p2 ∧ p1) → (p2 ∧ p4))) → p2) ∨ (p1 → (False → (False ∧ False))))) ∨ p3) ∨ (p1 ∨ (p3 ∨ ((p1 → p1) → True)))) := by
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
theorem thm_5_vars_150304809148473602565112085184 : ((p4 → (((p3 → (p5 ∧ p1)) ∨ False) ∧ (p2 → ((False ∧ True) ∨ (p1 ∨ (((p3 ∨ p4) ∧ True) ∧ False)))))) ∨ (True ∧ ((False ∨ True) ∨ p2))) := by
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
theorem thm_5_vars_191212923642825684050319313201 : (((True ∧ (True → p2)) → ((p5 → True) → (p5 ∧ p5))) ∨ ((((((p3 ∧ p5) ∨ (True ∨ p4)) → (True ∨ (p3 ∧ p5))) ∨ p2) ∧ False) → False)) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67766773134549448156346000021 : ((p2 → ((((p4 ∨ (p5 ∧ (False ∨ p2))) ∨ (False ∧ False)) ∨ (True ∨ ((True ∨ ((p1 → ((p4 → False) → p3)) ∧ p4)) → False))) ∨ p1)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48968139055289031426443710323 : ((((((p4 ∨ (((True ∧ (p4 ∨ False)) ∨ ((True → (p3 → (p3 ∨ p4))) → p3)) ∨ p1)) ∧ p5) → p3) ∨ p1) ∨ (True ∨ (p3 ∧ p1))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218496827271260469984245010075 : (((p1 ∨ p3) → (p4 ∧ p1)) → (p2 ∨ ((((p5 ∨ (p5 ∨ (p2 ∧ p5))) ∧ p2) ∧ (p5 ∧ (p5 → False))) → ((False ∧ p4) ∧ (p3 ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h11 := h9 h10
    -- False on the left can always be used.
    apply False.elim h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h4.left
      let h15 := h4.right
      -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
      have h16 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h14
      -- We have shown the premise of h15, we can now drive its conclusion.
      let h17 := h15 h16
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h4.left
      let h22 := h4.right
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h23 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h21
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h24 := h22 h23
      -- False on the left can always be used.
      apply False.elim h24
  -- Conjunctions on the left can always be decomposed.
  let h25 := h2.left
  let h26 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h27 := h25.left
  let h28 := h25.right
  -- Disjunctions on the left can always be decomposed.
  cases h27
  case inl h29 =>
    -- Conjunctions on the left can always be decomposed.
    let h30 := h26.left
    let h31 := h26.right
    -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
    have h32 : p5 := by
      -- One of the premise coincides with the conclusion.
      exact h30
    -- We have shown the premise of h31, we can now drive its conclusion.
    let h33 := h31 h32
    -- False on the left can always be used.
    apply False.elim h33
  case inr h34 =>
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h26.left
      let h37 := h26.right
      -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
      have h38 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h37, we can now drive its conclusion.
      let h39 := h37 h38
      -- False on the left can always be used.
      apply False.elim h39
    case inr h40 =>
      -- Conjunctions on the left can always be decomposed.
      let h41 := h40.left
      let h42 := h40.right
      -- Conjunctions on the left can always be decomposed.
      let h43 := h26.left
      let h44 := h26.right
      -- We want to use the implication h44 based on <expert-advice>. So we show its premise.
      have h45 : p5 := by
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h44, we can now drive its conclusion.
      let h46 := h44 h45
      -- False on the left can always be used.
      apply False.elim h46
  -- Conjunctions on the left can always be decomposed.
  let h47 := h2.left
  let h48 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h49 := h47.left
  let h50 := h47.right
  -- Disjunctions on the left can always be decomposed.
  cases h49
  case inl h51 =>
    -- Conjunctions on the left can always be decomposed.
    let h52 := h48.left
    let h53 := h48.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h52
  case inr h54 =>
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h55 =>
      -- Conjunctions on the left can always be decomposed.
      let h56 := h48.left
      let h57 := h48.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h56
    case inr h58 =>
      -- Conjunctions on the left can always be decomposed.
      let h59 := h58.left
      let h60 := h58.right
      -- Conjunctions on the left can always be decomposed.
      let h61 := h48.left
      let h62 := h48.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h61



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55241467664065601246437615471 : ((((p4 ∧ p5) ∧ (p1 → (p4 ∨ p5))) ∨ (True → (((((False ∧ p5) ∨ True) ∨ p1) → ((p2 → False) → (p4 ∧ (p2 ∨ p5)))) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116358827250559809045511005443 : ((((p3 → False) ∨ False) → (((True ∨ p2) ∨ p3) ∧ ((True ∨ p1) ∧ ((p2 → p1) ∨ (False ∨ ((True ∨ (p3 ∨ p5)) → False)))))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160485292176096904259509907905 : (((((((False ∧ (False → p4)) → p1) ∨ (False ∧ p5)) → p1) ∧ p5) ∧ ((True ∨ True) ∧ (False ∨ p4))) → ((p2 ∧ (p2 → False)) ∨ (p4 → p4))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h11
      -- One of the premise coincides with the conclusion.
      exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h15
      -- One of the premise coincides with the conclusion.
      exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352460532928705075865676799439 : (p4 → (((p2 ∧ True) → p3) → ((p2 ∨ p5) ∨ (((p4 ∧ (p5 ∨ ((p2 → (p5 ∧ ((p3 ∧ False) ∧ p1))) → False))) ∧ p4) → (p3 → p3))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h8
  case inl h9 =>
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758414840972733452012597909971 : (((p2 ∧ ((((False ∧ p2) ∧ p4) ∧ (False ∨ (((True ∧ True) ∧ (((False → ((p5 ∨ p1) ∨ p5)) → p1) → p5)) → (p5 ∧ p3)))) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675090532229967577421943381878 : ((((((False ∨ ((p4 → ((p5 ∧ p3) ∧ (p3 ∧ True))) → (((False ∨ False) → False) → p5))) ∧ p2) ∨ p2) ∧ (False ∨ ((p3 → p4) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_647921404048501813421462901994 : ((((((p2 ∨ (p4 ∨ (p5 → ((p2 → False) ∧ ((((False ∨ p1) ∧ (False ∨ True)) ∧ p4) → (p5 ∧ p5)))))) → p1) ∧ False) ∧ (p5 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190202964197547731272880644905 : (((p4 ∨ (p2 ∧ (p1 → (p3 ∧ (p5 ∨ True))))) ∧ True) ∨ (((p1 ∨ False) → p4) ∨ (((p4 ∧ (p2 → (False ∧ p2))) ∧ p3) ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_321069186988894523063698218598 : (p4 ∨ (p1 ∨ (((((((p5 → p2) ∨ p3) ∧ (p1 ∨ p1)) ∧ (p4 → p1)) ∧ (p5 ∨ True)) ∧ p5) ∨ (p4 → (p3 → (False ∨ (p2 → p3))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212161234951549292689009982875 : ((True ∨ ((False → p5) ∨ p3)) ∧ ((((((True → (p1 ∧ p3)) ∨ True) → ((p3 ∧ p1) ∧ (p4 ∨ p4))) ∨ ((p1 ∧ p4) ∧ p5)) ∧ p1) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_539259566513738275078897828 : ((((((p5 → ((p5 ∧ (p5 → (True ∧ False))) ∨ p5)) → (True → (p3 ∨ ((True ∨ True) ∨ True)))) ∨ p4) → (p1 → p3)) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37606986695479095473280900184 : (((((((p4 ∨ p1) ∧ ((((False ∧ p2) → (((False → False) ∨ p1) ∨ p2)) ∨ True) ∨ p1)) ∨ (p3 → (p3 ∨ p1))) ∧ p4) → p5) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253006343933551166343042202510 : ((True ∧ p3) → (((p5 ∧ (p5 ∧ (((p2 ∧ p3) ∧ p4) ∧ (p3 ∨ (p1 ∧ (False ∨ (p2 ∨ p1))))))) ∨ (p4 ∨ (p2 → p3))) ∨ (True ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114147414570124583311854390256 : (((((p3 ∧ (p1 ∨ (p2 ∧ ((False ∧ ((p1 ∧ (p3 ∧ p3)) → p3)) ∧ (p2 ∨ p5))))) → p4) ∨ False) → (False ∧ (p3 ∨ p2))) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209570079876743558453482459420 : ((p5 → ((True → p4) ∧ (p4 ∧ p3))) → (True ∧ ((((p1 → p3) ∨ p3) ∧ ((((p4 ∧ (p2 ∧ p2)) ∧ (p4 ∧ False)) → p5) → p1)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 ∧ (p2 ∧ p2)) ∧ (p4 ∧ False)) → p5) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Conjunctions on the left can always be decomposed.
      let h14 := h9.left
      let h15 := h9.right
      -- False on the left can always be used.
      apply False.elim h15
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h6
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h17 : p1 := by
      -- One of the premise coincides with the conclusion.
      exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h18 := h5 h17
    -- One of the premise coincides with the conclusion.
    exact h18
  case inr h19 =>
    -- One of the premise coincides with the conclusion.
    exact h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_551223381466055714926000319269 : (((p1 ∨ ((((True → False) ∨ (p2 ∧ p2)) ∨ p4) ∨ ((p3 ∨ ((p5 ∧ ((p4 ∧ True) ∧ (p1 ∨ p3))) → (True → True))) ∨ (p3 → True)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324562740733403366682776434750 : (p5 ∨ ((p1 → (p4 → (p1 → True))) → ((p3 ∨ p5) → ((p3 → (p4 ∧ (p5 ∨ (p5 ∨ (p4 → (False ∨ (False ∧ p5))))))) ∨ (True ∨ p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119399659366549647307861220148 : ((p4 → ((((p2 ∧ p2) ∧ ((((p5 → (False ∧ p2)) → (((p5 ∧ p4) ∧ p4) ∧ False)) ∨ p2) ∨ (p1 ∧ p5))) ∨ p3) ∨ False)) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125925730731850223293474238533 : (((True ∨ p5) → ((((p2 ∧ (((p3 ∨ (p4 ∧ p1)) ∧ p5) ∨ (True → (((True → p3) → p3) ∧ p5)))) → p2) ∧ p4) ∧ False)) → (p3 → p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328523368099313183820291816582 : (True → (((p1 ∨ (p4 ∧ (p3 ∨ (p4 ∨ p4)))) ∨ (p3 ∧ (((p1 ∧ True) ∧ p5) ∧ p1))) ∨ (p5 → (p2 → (((p5 → p5) → True) ∧ p5))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253889646177379543308677498733 : ((p1 ∧ p3) → (p2 ∨ (((((p2 ∧ (p4 → ((True → ((False ∨ p3) → False)) ∧ p1))) ∨ (p1 → p5)) ∨ p2) → (False ∧ p4)) ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612890955060033989499476633079 : (((((False ∨ (((False → p3) ∨ (p5 → (p4 → p4))) → (p5 → (((p4 ∧ True) ∧ (p5 → (False → p3))) ∨ p4)))) ∨ (p1 ∧ p4)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53108145222255032989121629300 : (((False → ((False ∧ p4) → ((p1 ∨ (p2 ∧ (p2 ∧ False))) ∧ p5))) ∧ ((((p4 ∨ p4) ∧ p5) → ((p2 → p4) → p3)) ∧ (False → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149565918954020953242202131389 : ((p2 ∧ (False ∧ (((((p2 → (p3 ∧ p3)) ∨ p4) → False) ∨ p4) → (((True → False) → (p5 → p3)) → p3)))) ∨ ((False → True) ∨ (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66464649055365281296139935455 : ((True → ((p1 ∨ ((p2 ∧ ((p2 → p3) → ((True ∧ ((p4 ∨ (((False ∨ p2) → True) → p3)) ∧ p2)) ∨ (p3 ∨ p2)))) ∨ p5)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136903820432662302161356491011 : (((p5 ∨ p3) ∨ (((p5 ∧ (p2 → ((p3 ∧ p1) → p2))) ∨ ((((p4 ∨ p4) ∨ (p3 ∧ p2)) ∧ p1) → False)) ∧ False)) ∨ (p1 → (p1 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115443169212742455561264510551 : (((((p1 ∨ (p5 → p4)) ∧ p4) → (p5 ∨ p3)) ∨ (False → (((p5 → False) ∨ (False ∧ (False ∧ p3))) → ((p3 ∨ True) ∨ True)))) ∨ (p2 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h1
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111622783663931064255325955895 : ((((((p2 ∨ False) ∨ ((p1 ∨ p1) ∧ (((False ∧ ((p5 ∨ p4) ∧ (p1 → False))) ∨ True) ∨ p1))) ∧ (p1 ∨ True)) ∨ p4) ∨ True) ∨ (p5 → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



