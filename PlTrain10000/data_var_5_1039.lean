variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18151431298503736919153685770 : (((((p4 ∨ ((False ∧ True) → p4)) ∧ (((True ∧ p4) → (p1 → True)) → (p2 ∧ (p2 ∧ p1)))) ∧ p5) → ((p5 ∧ (p2 → p5)) ∧ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h1.left
  let h10 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h9.left
  let h12 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Conjunctions on the left can always be decomposed.
  let h15 := h1.left
  let h16 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h17 := h15.left
  let h18 := h15.right
  -- Disjunctions on the left can always be decomposed.
  cases h17
  case inl h19 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h20 : ((True ∧ p4) → (p1 → True)) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h23 := h18 h20
    -- We need to get the right conjuct of h23 based on <expert-advice>.
    let h24 := h23.right
    -- We need to get the right conjuct of h24 based on <expert-advice>.
    let h25 := h24.right
    -- One of the premise coincides with the conclusion.
    exact h25
  case inr h26 =>
    -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
    have h27 : ((True ∧ p4) → (p1 → True)) := by
      -- Implications on the right can always be decomposed.
      intro h28
      -- Implications on the right can always be decomposed.
      intro h29
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h18, we can now drive its conclusion.
    let h30 := h18 h27
    -- We need to get the right conjuct of h30 based on <expert-advice>.
    let h31 := h30.right
    -- We need to get the right conjuct of h31 based on <expert-advice>.
    let h32 := h31.right
    -- One of the premise coincides with the conclusion.
    exact h32
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248270333993689400864419122256 : ((p2 ∨ p2) ∨ ((p3 → (((p4 ∧ p1) ∨ (((True → p2) ∧ False) → p1)) → ((p4 → (p1 ∧ p5)) ∨ (p3 ∧ (p2 → p2))))) ∨ (p3 ∧ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h1
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_3917710748225291123092787608 : (False ∨ ((((p2 ∨ (((((p3 ∨ p5) → p2) → p5) ∧ True) ∧ p4)) ∨ (p2 → (p5 ∨ (p5 ∧ p2)))) ∨ True) ∨ (p5 ∧ (p1 ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38919594890210970023803455342 : ((((p5 → (p4 ∨ p1)) ∨ (((p1 → (p3 → ((((False → (p4 ∧ p4)) ∨ p5) ∧ p1) ∨ (p3 → p5)))) ∧ (p1 ∨ True)) → False)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16958425455189014348475816851 : (((p3 ∨ (((False ∨ ((True ∨ p2) → p4)) ∧ p3) ∨ ((p5 → (p5 ∧ ((False ∨ p1) → True))) → (p2 ∨ p3)))) ∨ (p2 ∨ (False → p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_323519337611909207011774720437 : (p5 ∨ ((p4 ∧ (((False ∧ (p4 ∨ p4)) ∧ p2) ∨ ((p4 → (p4 ∧ ((p1 → p3) ∧ p2))) → (True ∧ (True ∨ p2))))) ∨ (False → (p2 → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348831195907524002902406370774 : (p3 → (p1 ∨ (False ∨ ((p2 ∨ ((p1 → ((p3 ∧ ((False → p3) → p3)) ∧ ((p4 ∧ p1) ∨ (p5 ∨ ((False → True) ∨ p5))))) → p1)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113103872712765285484026472567 : (((True → (((p1 ∨ p4) → ((False ∧ p3) → ((False ∨ p3) ∨ p5))) ∨ ((p4 ∧ p2) ∧ ((p5 ∨ p5) → (p1 ∧ True))))) → p3) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58086837315128496322264521663 : (((p1 ∧ False) ∧ (((((p4 ∧ (p1 ∨ p2)) ∧ ((p2 → True) ∨ True)) ∧ p5) ∧ ((p3 ∧ True) → p4)) ∧ (p3 → (p2 ∧ (p4 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217381275748510703809844424815 : (((p5 ∨ (False ∨ False)) ∨ p1) → (p4 ∨ (((p3 → (p2 ∨ p1)) ∨ (p3 ∨ p2)) ∨ (((p5 → False) → p2) ∨ (True → (False ∨ (p5 ∨ p2))))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258795245407818943539671238370 : ((True → False) → (((p5 ∨ p5) → True) → ((p4 → (((p1 → ((((p5 → p4) ∧ p4) → (p5 ∧ p3)) ∨ False)) ∧ p2) → p5)) ∨ (True ∧ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217913100845284427301276605874 : (((p4 → (p5 ∨ p2)) → p4) → ((p4 → (((False → (False ∨ (False ∧ p5))) ∧ False) ∧ p3)) → (p2 ∧ (True ∨ ((False → (p4 ∧ p1)) → False))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 → (p5 ∨ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- False on the left can always be used.
    apply False.elim h8
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h10 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h11 := h2 h10
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We need to get the right conjuct of h12 based on <expert-advice>.
  let h13 := h12.right
  -- False on the left can always be used.
  apply False.elim h13
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694327765569920358207963796115 : ((((((p2 → p4) ∧ p1) → (((p3 ∧ p3) ∧ (p3 → (True ∨ p1))) → False)) ∨ (p3 ∨ ((True ∨ p2) ∨ ((p1 ∨ p1) ∨ (p1 → p4))))) ∨ p3) ∧ True) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124120015783003216614504427595 : (((((True → True) ∧ p5) ∨ (False ∨ ((p2 ∧ p3) ∨ True))) ∧ (True → (((p4 → (True ∧ (p2 ∨ p1))) ∧ (False ∧ p4)) ∧ p5))) → (p5 ∨ p5)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Conjunctions on the left can always be decomposed.
        let h11 := h10.left
        let h12 := h10.right
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- We need to get the left conjuct of h14 based on <expert-advice>.
        let h15 := h14.left
        -- We need to get the right conjuct of h15 based on <expert-advice>.
        let h16 := h15.right
        -- We need to get the left conjuct of h16 based on <expert-advice>.
        let h17 := h16.left
        -- False on the left can always be used.
        apply False.elim h17
      case inr h18 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h19 : True := by
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h20 := h3 h19
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- We need to get the right conjuct of h21 based on <expert-advice>.
        let h22 := h21.right
        -- We need to get the left conjuct of h22 based on <expert-advice>.
        let h23 := h22.left
        -- False on the left can always be used.
        apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54713787574178582035674846316 : ((((((p2 → True) → p5) ∨ p5) → (True → True)) → ((p3 ∨ (((p1 ∧ False) ∧ (p2 → p4)) ∧ (p5 → True))) ∧ ((False ∨ p4) → p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166407429100736538534227988399 : ((p1 ∨ (((((p2 → p3) ∧ p2) ∧ p2) ∨ ((p2 → False) ∨ ((p1 ∨ p2) → p2))) ∧ p3)) ∨ (((p4 ∨ (p1 → (p4 ∨ p1))) ∨ p4) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319576683261409762663298676256 : (p4 ∨ ((((p3 → False) ∧ (p5 → p5)) ∧ ((True → False) ∧ p4)) → ((((p4 → p1) ∨ p5) → (p2 ∨ (((False ∧ p2) ∨ True) ∧ p5))) ∨ p4))) := by
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
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39012454074420560480958482950 : ((((p5 ∨ p1) ∧ (((p3 ∧ (((p5 → (False ∨ ((p3 ∧ p3) → (p1 → p2)))) → p3) ∨ (False ∧ p4))) ∧ (p2 ∨ p3)) ∧ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_210466395732571454862670563068 : (((False → (p5 → p3)) ∨ False) ∧ ((p5 → (((((p5 ∧ (((p1 ∨ p3) ∨ p2) → p1)) → True) → p1) ∧ p1) ∨ ((True ∨ p5) ∨ True))) ∨ p5)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207453035219840215031470540354 : (((p5 ∨ ((True ∧ p4) ∧ p1)) ∨ p1) → (((p5 → ((p3 ∨ p2) ∨ (p2 ∨ p5))) ∨ (((p5 ∧ p2) ∨ (p3 ∧ (p3 ∧ p5))) ∧ True)) ∨ p1)) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h4
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Conjunctions on the left can always be decomposed.
      let h8 := h6.left
      let h9 := h6.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318603638325446596144951838823 : (p4 ∨ (((False ∧ ((((p3 → True) ∨ True) ∧ False) ∧ p4)) ∨ (False ∧ (False → ((((p5 ∧ p3) ∧ False) ∧ p4) → (True ∧ p3))))) ∨ (True ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39179265985284416892567628717 : ((((p1 → p3) → (p3 ∨ (((p2 → p1) ∨ ((p5 ∨ p1) → (p2 ∨ True))) ∨ (((p3 ∧ True) → False) ∧ ((p3 ∨ p4) → False))))) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213300632481537641621342035763 : (((True ∧ (p1 ∧ p5)) ∧ p3) ∨ ((p2 ∧ (((False ∧ p5) → True) ∧ (((p2 → p5) ∨ p4) ∨ (p5 ∨ False)))) → (p1 ∨ (p2 ∧ (True ∨ p5))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- One of the premise coincides with the conclusion.
      exact h2
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h11 =>
      -- False on the left can always be used.
      apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49789174999108387216269684404 : (((p4 ∨ (((p4 ∨ (p4 ∧ p5)) ∨ p1) → ((((p1 → False) ∨ (True ∨ p3)) → (p4 → (True ∧ p5))) ∧ p5))) → (p5 → (p5 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171860500774156724116417571078 : (((True ∧ ((((False ∨ (True ∨ (p4 ∧ p5))) ∧ True) → False) → (p2 ∧ p4))) → False) ∨ (False → (p2 → ((((False ∨ True) ∨ True) ∨ p2) ∧ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159199432135975630295625782681 : ((p2 → ((p2 ∨ ((((True ∨ p5) → (False → True)) ∨ p4) ∧ (((p2 ∨ False) ∨ True) → p1))) → False)) ∨ ((False ∨ (False → False)) ∨ (True → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722433528826804749065296526278 : (((((True ∨ p1) ∧ p3) ∧ ((((p5 → True) ∧ p1) ∧ ((p1 → ((True ∧ ((p4 → p1) ∧ p2)) ∨ p2)) ∧ (p3 → (p3 ∨ p3)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215880304470616940946116561132 : ((p3 ∨ ((p3 ∧ False) ∧ p4)) ∨ ((((p5 → (False → (True ∧ (p4 → p3)))) ∧ (p2 ∧ p5)) → ((True → True) → p5)) ∧ (p3 ∨ (False → False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690633449135592562471579091517 : (((((((False → p1) ∧ (False ∨ p5)) ∧ ((((True ∨ p3) ∧ p4) ∨ False) ∨ p1)) ∨ p1) → (p2 ∧ (p3 ∨ ((True ∧ False) ∧ (False → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246336536555827070710023280866 : ((p4 ∧ p5) ∨ ((((((((p2 → p2) ∨ p2) → True) ∨ False) → p2) → p1) ∧ p4) ∨ ((True ∧ True) ∧ (p5 ∨ ((p5 ∧ p4) → (p3 ∨ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_685080527016186401848028637755 : ((((False ∨ (p5 ∨ (False ∨ ((p2 → False) ∨ (True ∧ ((False → True) ∧ (p3 → (p2 ∨ p3)))))))) ∨ ((((p5 → p5) ∨ True) ∨ p2) → p2)) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137746741635336440285532542199 : ((p2 ∨ ((False ∧ ((p2 ∧ True) → ((((p5 ∨ (p3 ∧ True)) → (p5 → ((p5 ∨ False) ∧ p4))) ∨ p5) → p1))) ∧ p5)) ∨ ((p4 → p3) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46970364613411677396220510543 : (((((((((p1 ∧ p4) ∨ (True → False)) ∧ False) → (p4 ∧ ((((p1 → True) ∨ p2) ∨ p5) → p3))) → p1) → p3) → p2) ∨ (p3 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40106058990681092240840600411 : (((((p5 → ((True ∧ p2) ∨ ((p3 ∨ (p2 ∧ (((False → p2) → p5) → False))) ∨ ((False ∨ p1) ∧ p2)))) ∧ (p5 ∨ True)) ∧ p4) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358156072240989951989681339183 : (p5 → (p3 ∨ (((((True ∨ (p3 → p2)) ∧ (p5 ∧ (p5 ∧ (((True ∨ p2) ∨ p5) ∨ (p5 ∨ p4))))) → p1) ∨ ((False ∧ True) → p5)) ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711145867857140491886213150040 : ((((p1 ∧ (p1 ∨ (p3 ∨ (p1 → p1)))) ∧ (p5 ∧ (p5 ∨ ((p3 → (p3 → p4)) ∧ (((False ∨ (p5 ∧ (False → p4))) → p5) ∨ p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263704957965141633351272547994 : (True ∧ ((p1 ∧ ((p1 → (((p2 ∨ p4) ∧ (p4 → True)) → p5)) ∨ ((p3 → (p3 → False)) ∧ p4))) ∨ (p3 → (p3 ∨ ((p1 ∨ p2) ∧ True))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336124250829894003930749737083 : (p1 → (((((True ∧ p1) ∧ ((p5 → (p3 ∨ p4)) ∨ (p3 → p4))) ∧ ((True → (p3 ∨ ((p3 → (p3 ∨ False)) ∧ p5))) → p5)) ∨ p1) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_738413470328800445003979119105 : ((((p1 ∧ p1) ∨ (False ∨ (((((((True → p5) ∧ p5) ∨ p4) ∧ (False ∨ (False → ((p3 ∧ p5) → p1)))) → p3) → (p2 ∧ p3)) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300425076423848564169052088913 : (False ∨ (((((False ∨ p1) → (p3 → ((p5 ∧ ((p3 → (p2 ∧ (p2 ∧ p3))) ∧ (True ∨ p2))) ∨ p2))) ∨ p5) ∨ False) → ((False ∧ False) ∨ True))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135475394742549727361332336734 : ((((((((p5 ∧ p5) → p2) ∧ p3) → p1) ∧ True) ∧ ((False ∨ ((p3 ∧ p3) → False)) ∨ p3)) → ((p4 ∧ p1) → p1)) ∨ ((p3 ∨ p5) → p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- False on the left can always be used.
      apply False.elim h10
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h12 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64406102809512963301418989562 : ((p1 ∨ (((False → (p2 → ((True ∧ p2) ∧ p5))) ∧ ((((p5 ∧ p5) ∧ (p5 ∨ (False → (True ∧ True)))) ∨ p3) ∧ (p5 → p3))) → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_250054991973771196900191415427 : ((True → p3) ∨ ((False → p3) → (p3 ∨ ((True → p4) → (p3 ∨ (((p3 ∧ (p3 ∧ False)) ∨ True) ∨ (False ∨ ((p1 ∨ (False ∨ True)) ∧ p4)))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66192337134954203783902243161 : ((p5 ∨ ((p3 ∧ ((((p5 → (False ∧ p3)) ∧ p3) → ((False ∧ (p5 ∧ p2)) ∧ p5)) → p4)) ∧ (p5 ∧ (True → ((p3 ∨ True) ∧ p2))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247435357939446627492397708594 : ((False ∨ p2) ∨ ((((p5 ∨ p4) ∧ p1) ∧ p2) ∨ (((True ∧ False) → p3) ∧ ((p3 ∨ p3) → (p3 ∧ (((p3 ∧ p2) → p2) ∧ (p1 ∨ True))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h10 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h9
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228821887704085487164439892558 : ((p3 ∨ (p4 ∨ p5)) ∨ (((False ∨ p4) ∧ (((p5 ∧ (((p2 ∨ p3) ∨ (False → ((p2 ∧ False) ∨ False))) → (p4 → p3))) ∨ False) ∨ p3)) → p3)) := by
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
    apply False.elim h4
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h10 : ((p2 ∨ p3) ∨ (False → ((p2 ∧ False) ∨ False))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h11
          -- False on the left can always be used.
          apply False.elim h11
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h10
        -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
        have h13 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h5
        -- We have shown the premise of h12, we can now drive its conclusion.
        let h14 := h12 h13
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- False on the left can always be used.
        apply False.elim h15
    case inr h16 =>
      -- One of the premise coincides with the conclusion.
      exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61587971573122350102707489802 : ((p1 ∧ (((False ∨ p2) → p2) ∧ (p1 → (p3 ∨ ((p5 → (((p4 ∨ p3) ∨ (((p2 → (p3 → p5)) ∨ p2) → p2)) ∨ p5)) ∧ p1))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711217859075032861976992075669 : ((((p4 ∧ ((p1 ∨ (False → p4)) ∧ False)) ∧ (((p2 → (p2 ∧ p5)) ∨ (p2 ∨ p4)) ∨ ((p4 → False) ∨ (p4 → (p3 → (p5 ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712883985579863376581609475966 : (((((p4 → p1) → (p4 → (p2 ∧ p4))) ∨ (p1 → ((((p4 ∨ p1) ∧ ((False ∧ (((p3 → p5) → p5) → p5)) ∨ p5)) ∨ p4) ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696845971211191687673395281065 : ((((((((p4 ∨ p2) ∧ (p4 ∧ p4)) ∧ p3) ∨ p4) ∧ (False ∧ p1)) ∧ (((((p3 ∨ False) ∨ (p2 ∧ p4)) ∨ p4) → False) ∧ (True → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197981900128757277684997651839 : (((p2 ∨ p3) ∧ (p4 ∧ ((p2 ∨ p3) ∨ p4))) ∨ (p2 → ((True ∨ (p3 ∧ p4)) ∨ ((p4 ∨ (p1 ∨ ((p1 ∨ (p4 → p1)) ∧ p5))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61246696408034983320978926262 : ((False ∧ (p5 ∧ (((False ∧ (p5 ∨ p2)) ∧ (p1 → (p4 ∨ (p4 ∨ (((p3 ∧ (p5 ∧ (True ∨ (p1 ∧ p5)))) ∧ p5) ∨ True))))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313988611611702416004614813710 : (p3 ∨ (((p1 ∨ ((True → True) → p4)) → (p4 → ((((True ∨ (p5 ∨ p5)) ∨ True) → ((False ∧ True) ∧ (True → True))) ∨ p4))) ∨ (p1 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228783849840616510019413166347 : ((p3 ∨ (p5 ∧ True)) ∨ (p5 ∨ (((p4 ∨ ((p3 ∨ False) → p1)) ∧ (p3 ∧ (p4 ∧ ((((p4 → True) ∨ p3) ∧ True) ∧ (p4 → p4))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148100256111858497684150584686 : (((((p1 → p2) ∧ ((((((p1 → True) ∧ p3) ∧ p4) ∨ p4) ∧ p3) → p3)) ∨ (p2 ∨ p4)) → (p4 → p2)) ∨ (False ∨ ((p1 → True) ∨ False))) := by
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
theorem thm_5_vars_216642658767825832154412020420 : ((((True ∨ True) ∨ p4) ∧ p5) → ((((p2 ∨ (p5 → p5)) ∧ True) ∧ ((((p5 ∨ p2) → (((p1 ∨ p4) ∧ p4) ∨ p5)) → p2) ∧ True)) → p2)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h4.left
    let h9 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h10 := h1.left
    let h11 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h14 =>
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h15 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h16 =>
    -- Conjunctions on the left can always be decomposed.
    let h17 := h4.left
    let h18 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h19 := h1.left
    let h20 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h19
    case inl h21 =>
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h23 : ((p5 ∨ p2) → (((p1 ∨ p4) ∧ p4) ∨ p5)) := by
          -- Implications on the right can always be decomposed.
          intro h24
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h25
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h27 := h17 h23
        -- One of the premise coincides with the conclusion.
        exact h27
      case inr h28 =>
        -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
        have h29 : ((p5 ∨ p2) → (((p1 ∨ p4) ∧ p4) ∨ p5)) := by
          -- Implications on the right can always be decomposed.
          intro h30
          -- Disjunctions on the left can always be decomposed.
          cases h30
          case inl h31 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h31
          case inr h32 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h20
        -- We have shown the premise of h17, we can now drive its conclusion.
        let h33 := h17 h29
        -- One of the premise coincides with the conclusion.
        exact h33
    case inr h34 =>
      -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
      have h35 : ((p5 ∨ p2) → (((p1 ∨ p4) ∧ p4) ∨ p5)) := by
        -- Implications on the right can always be decomposed.
        intro h36
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h37
        case inr h38 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h20
      -- We have shown the premise of h17, we can now drive its conclusion.
      let h39 := h17 h35
      -- One of the premise coincides with the conclusion.
      exact h39



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720657507620739424786600719617 : ((((((p2 → True) ∨ p3) → p5) → (p3 ∧ (((False → ((p5 → p5) ∨ p1)) ∧ p3) ∨ (((p4 → ((p3 ∧ p2) ∨ p5)) ∨ p4) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727505780445119464076566487958 : ((((p4 ∧ (p3 ∧ False)) ∨ (True ∧ (((False ∨ ((((p1 → p1) ∧ ((p4 ∧ p4) ∨ p2)) ∨ ((p5 → True) ∨ p4)) ∧ p5)) ∧ p3) ∨ True))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_594579435521298671749604255495 : (((((p5 ∧ (False ∨ (p5 ∨ ((True ∨ (p3 ∧ ((p4 → p1) ∨ (False ∨ p4)))) ∧ False)))) ∨ (p4 ∧ (p4 ∧ ((True ∨ p4) → p3)))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217317253124649411731701816196 : (((True ∨ (p4 ∨ False)) ∨ p2) → ((True ∨ ((((False → p5) ∧ (p5 ∧ (False → (p1 → p2)))) → p3) ∨ p1)) → (p3 → ((False ∨ p1) ∨ True)))) := by
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
    cases h1
    case inl h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h9 =>
          -- False on the left can always be used.
          apply False.elim h9
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h13
        case inl h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h15 =>
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h16 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h17 =>
            -- False on the left can always be used.
            apply False.elim h17
      case inr h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h22 =>
          -- Disjunctions on the left can always be decomposed.
          cases h22
          case inl h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h24 =>
            -- False on the left can always be used.
            apply False.elim h24
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47865153230693898126491306677 : (((((False ∨ ((((p4 ∧ (p3 ∨ (p1 ∨ p5))) ∧ (False ∧ p2)) ∨ (p1 → True)) ∨ False)) ∨ (p3 ∨ p2)) ∧ (True → False)) → (False ∨ p1)) ∨ p1) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Disjunctions on the left can always be decomposed.
        cases h7
        case inl h8 =>
          -- Conjunctions on the left can always be decomposed.
          let h9 := h8.left
          let h10 := h8.right
          -- Conjunctions on the left can always be decomposed.
          let h11 := h9.left
          let h12 := h9.right
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h10.left
            let h15 := h10.right
            -- False on the left can always be used.
            apply False.elim h14
          case inr h16 =>
            -- Disjunctions on the left can always be decomposed.
            cases h16
            case inl h17 =>
              -- Conjunctions on the left can always be decomposed.
              let h18 := h10.left
              let h19 := h10.right
              -- False on the left can always be used.
              apply False.elim h18
            case inr h20 =>
              -- Conjunctions on the left can always be decomposed.
              let h21 := h10.left
              let h22 := h10.right
              -- False on the left can always be used.
              apply False.elim h21
        case inr h23 =>
          -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
          have h24 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h3, we can now drive its conclusion.
          let h25 := h3 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- False on the left can always be used.
        apply False.elim h26
  case inr h27 =>
    -- Disjunctions on the left can always be decomposed.
    cases h27
    case inl h28 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h29 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h30 := h3 h29
      -- False on the left can always be used.
      apply False.elim h30
    case inr h31 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h32 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h33 := h3 h32
      -- False on the left can always be used.
      apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46527620363224644763477989253 : ((((p1 ∧ p4) ∨ (((True ∨ (((p4 → p3) ∨ p3) → p2)) ∧ p4) ∧ (((p3 ∨ (p4 ∧ (True ∨ False))) ∨ p5) ∨ p1))) ∧ (p1 → p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204206511707179272945592072050 : (((((p1 ∨ False) → p4) → p3) ∧ p3) ∨ (p2 ∨ (((p1 ∨ (((p5 → True) ∨ p1) → (p3 ∨ p2))) ∨ True) ∨ ((True → (True → p2)) ∧ True)))) := by
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
theorem thm_5_vars_191009802982225626151017444767 : (((False ∨ ((p5 → True) → False)) ∨ (p3 ∧ (p5 → p1))) ∨ (((True → False) → p3) → (((p5 ∧ (p1 ∧ (False → (p2 → p1)))) ∨ p2) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328704055403938134335666181312 : (True → ((((p4 ∨ p4) ∨ (p3 ∧ (p5 ∨ True))) ∨ (p5 ∧ (p3 → p4))) ∨ ((False → p3) ∨ (((p5 → (p1 ∧ (p1 → p2))) → p2) ∧ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303945333897929376848793718386 : (p1 ∨ (((False ∨ (p1 ∨ (p1 → (p2 ∨ p1)))) → (p4 ∧ (((p1 → p3) ∧ ((((p2 → False) ∨ (p1 → p4)) ∨ p5) ∧ p1)) ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179658034413684984997680163233 : ((p5 → ((((False ∨ False) → p1) ∧ True) → (p3 ∧ (p3 ∨ (p5 → p3))))) ∨ ((p1 ∨ ((p1 → p4) → True)) ∨ (p5 → (True ∧ (p3 ∧ False))))) := by
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
theorem thm_5_vars_219566790748128347951799511715 : ((True → ((True → p2) ∨ p1)) → (((p4 ∨ (p4 ∨ False)) ∨ ((p2 → True) ∨ p3)) → (p4 ∨ ((p5 ∧ p4) → ((p2 → (False ∧ p3)) → p1))))) := by
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
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- False on the left can always be used.
        apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
        have h17 : p2 := by
          -- We want to use the implication h16 based on <expert-advice>. So we show its premise.
          have h18 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h16, we can now drive its conclusion.
          let h19 := h16 h18
          -- One of the premise coincides with the conclusion.
          exact h19
        -- We have shown the premise of h11, we can now drive its conclusion.
        let h20 := h11 h17
        -- We need to get the left conjuct of h20 based on <expert-advice>.
        let h21 := h20.left
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h23 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h24
      -- Implications on the right can always be decomposed.
      intro h25
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h28 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h29 := h1 h28
      -- Disjunctions on the left can always be decomposed.
      cases h29
      case inl h30 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h31 : p2 := by
          -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
          have h32 : True := by
            -- True on the right can always be proven directly.
            apply True.intro
          -- We have shown the premise of h30, we can now drive its conclusion.
          let h33 := h30 h32
          -- One of the premise coincides with the conclusion.
          exact h33
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h34 := h25 h31
        -- We need to get the left conjuct of h34 based on <expert-advice>.
        let h35 := h34.left
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- One of the premise coincides with the conclusion.
        exact h36



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111965232670052266070258486368 : ((((p3 → ((True ∨ p2) → ((False ∧ p3) ∨ p5))) → (p1 ∨ (((p5 → p2) ∨ ((p3 ∧ False) → p5)) ∨ (p4 ∧ False)))) ∨ p4) ∨ (p1 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165932154236921975642623634203 : (((p4 ∧ p5) ∧ (p2 ∧ ((True ∧ ((p3 ∧ p2) ∧ (p2 → ((False ∨ p1) ∧ False)))) ∧ False))) ∨ ((p3 ∨ (True → p3)) → ((True ∨ p2) ∨ p4))) := by
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
theorem thm_5_vars_113452074204073779036171072730 : ((((((True ∨ p2) ∨ (((False ∧ ((True ∨ True) ∨ p4)) → (p3 → ((p1 → p5) ∧ p4))) ∧ p5)) ∧ p5) → p3) ∨ (False → p5)) ∨ (False ∨ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156971806603438021121077905016 : (((((((p4 ∧ p2) → (False → (p4 ∧ p5))) → p4) ∨ False) → (p4 ∧ ((p1 ∨ p4) ∧ p2))) ∨ p3) ∨ ((False ∧ (p1 ∧ (p1 ∨ p4))) → p3)) := by
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
theorem thm_5_vars_47957307107890352181532489750 : ((((False ∧ (p1 ∧ ((p1 ∨ (((p2 ∨ p4) → (p4 ∨ ((p4 ∨ p5) ∧ p3))) → p4)) ∧ p1))) → (p1 ∧ (p2 → True))) → (True ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197118457939209870272386516402 : (((p1 ∨ (p3 ∨ (p5 ∧ (p1 ∨ p1)))) ∨ p1) ∨ (False → ((((p1 ∧ p1) → ((p4 ∧ p4) ∨ False)) ∧ ((p1 ∧ p2) ∨ True)) → (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h1
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111587165708774908343496860359 : ((((p1 ∨ ((((p4 ∧ (True ∨ True)) ∧ (True ∨ (((p3 ∨ p1) ∧ (p1 ∨ p3)) → p2))) ∧ (p2 → False)) ∧ p2)) ∧ p3) ∨ p3) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38637488705788910105912302236 : ((((p2 ∨ (((p1 ∧ p4) ∨ (p5 ∧ False)) ∧ True)) ∨ (((p1 ∨ ((p3 → True) ∧ ((p3 → True) ∧ True))) ∨ False) ∨ (p5 ∧ p4))) ∧ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612312316300825244445986048677 : (((((p2 ∧ (((((True ∧ p5) → p3) ∧ ((p2 → (p2 ∧ p2)) ∧ p3)) ∧ ((p3 ∧ (p2 → True)) → p1)) → p2)) ∧ (p4 ∧ p5)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234067490154302698455558198886 : ((True → (True ∧ p4)) → ((((False → (((p5 → p3) ∨ p3) → (p1 ∧ (p1 ∧ p2)))) ∧ p1) → ((p2 ∨ (True ∨ p4)) ∧ p1)) ∧ (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h5 := h2.left
  let h6 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181100467206841056705131671941 : (((p4 → False) → ((p4 → p5) ∧ ((p4 ∨ ((False ∨ True) ∧ p4)) ∧ p4))) → ((p5 → p2) ∨ ((p1 ∨ (p4 ∨ (False ∨ True))) ∨ (True ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66165855527978826261711218500 : ((p5 ∨ (((p4 ∧ (False ∧ (p2 ∧ (p2 ∨ ((p1 → p3) → (p4 ∨ (p4 → (p5 → True)))))))) ∨ (p3 ∧ p2)) ∨ ((False ∧ False) → True))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50682878042076356294151022432 : (((((False → (True ∧ True)) ∧ True) → (p4 → (p4 ∨ ((p4 ∨ p3) ∨ ((p2 ∧ p4) ∧ (p5 ∧ True)))))) → ((p2 ∨ False) ∧ (False → True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38135296310348995479674394022 : ((((True ∧ ((((True ∧ p4) ∧ p5) ∨ (True → ((False → (False → p3)) ∨ (False ∧ p4)))) ∧ (p3 → True))) ∧ ((False ∧ p3) ∧ p4)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49104759383062374843722744929 : ((((p3 ∨ (((p3 → p3) ∧ p4) → ((p2 ∨ (p3 ∨ ((p3 → p3) → False))) → p2))) → (p4 → (p3 ∨ False))) ∨ ((p5 → False) → True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704570328937318297176413862395 : (((((p4 ∨ p4) ∨ (p4 ∨ ((p4 ∧ p1) ∧ (False ∨ p2)))) → (((p4 → (p3 ∧ (False ∧ (p4 ∨ (p1 ∧ False))))) ∧ p3) → (p2 → False))) ∨ False) ∧ True) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h8 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h7
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h9 := h4 h8
      -- We need to get the right conjuct of h9 based on <expert-advice>.
      let h10 := h9.right
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- False on the left can always be used.
      apply False.elim h11
    case inr h12 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h13 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h12
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h14 := h4 h13
      -- We need to get the right conjuct of h14 based on <expert-advice>.
      let h15 := h14.right
      -- We need to get the left conjuct of h15 based on <expert-advice>.
      let h16 := h15.left
      -- False on the left can always be used.
      apply False.elim h16
  case inr h17 =>
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h19 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h20 := h4 h19
      -- We need to get the right conjuct of h20 based on <expert-advice>.
      let h21 := h20.right
      -- We need to get the left conjuct of h21 based on <expert-advice>.
      let h22 := h21.left
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Conjunctions on the left can always be decomposed.
      let h26 := h24.left
      let h27 := h24.right
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h28 =>
        -- False on the left can always be used.
        apply False.elim h28
      case inr h29 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h30 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h31 := h4 h30
        -- We need to get the right conjuct of h31 based on <expert-advice>.
        let h32 := h31.right
        -- We need to get the left conjuct of h32 based on <expert-advice>.
        let h33 := h32.left
        -- False on the left can always be used.
        apply False.elim h33
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_696948271837085713395553076474 : ((((((p4 ∧ ((p2 → (p4 ∨ p3)) → p4)) → True) → (p4 ∨ p3)) ∧ (((p1 ∨ (False ∧ p4)) ∧ ((False ∨ p4) → (p3 ∧ p5))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_125930795785776560682133075038 : (((False ∨ p1) → ((((p1 ∧ (p2 → (True ∨ p4))) → (((p2 ∨ False) ∨ p4) ∧ ((True → p3) → p1))) ∨ (p4 ∨ p4)) → p5)) → (p3 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213083748062657858251068921938 : ((((p3 ∧ p1) ∧ p3) ∧ p5) ∨ (((((p4 ∨ (p2 → ((False ∨ (((p3 → p5) ∨ p2) ∧ True)) → p4))) ∨ p2) → False) ∨ (False → p3)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40241586607942253161560625966 : ((((p4 ∧ (p2 ∨ (((p3 → p5) ∧ (p1 ∧ p3)) ∨ (p1 ∨ (((p1 ∧ False) ∨ (p2 → ((p2 ∧ True) ∧ False))) ∨ p1))))) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205166949244653481254352769850 : (((p5 ∧ (False ∧ True)) ∧ (p5 ∧ p5)) ∨ (False ∨ ((p2 → (p5 ∧ p1)) → (True ∧ (p3 → ((False → p3) ∨ (p2 → ((p1 ∨ True) ∨ p4)))))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137649837992595437890160924340 : ((False ∨ ((p2 → (p2 ∧ True)) ∧ ((((p2 → (p3 ∨ p1)) → p2) → p2) ∧ (((True ∧ p1) → p3) → (p5 → p4))))) ∨ ((p4 ∧ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_63926554732818427029449693827 : ((False ∨ (((True ∧ ((p4 → p1) ∧ ((p3 ∧ ((((p5 ∨ p1) ∨ p1) ∨ p3) → (p4 ∨ True))) ∨ (p3 ∧ (p1 ∧ True))))) ∨ True) ∨ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249961415466543999780188187078 : ((True → p2) ∨ ((p4 ∨ (((p4 → False) ∧ p3) ∧ (((False → False) ∧ (False ∨ (p2 → (False ∨ (p5 ∧ ((p1 → p2) → True)))))) ∧ p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52218061049434410948833421917 : ((((p5 ∧ p5) → (p4 → (p2 ∨ (((((p2 → p3) ∨ p4) ∧ False) ∧ True) → p3)))) → ((((p1 → True) ∨ (p1 → p2)) ∨ p5) → p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668372532369140030397055067845 : ((((p5 → (p2 → (((p4 → (((p3 ∨ p2) ∨ p3) ∧ p5)) ∧ p5) → ((p3 ∧ (False ∨ p4)) ∧ (p2 ∧ p2))))) ∧ (p1 → (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213174669469974547525443792280 : ((((False ∨ True) ∨ p5) ∧ p2) ∨ (p3 → ((((p5 ∨ ((p4 ∧ (((((p2 ∨ True) ∧ True) → p4) → False) ∧ p4)) → True)) ∧ False) ∨ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727325516119509375806428628903 : ((((p1 ∧ (p3 → False)) ∨ (((p4 → (p2 ∨ (p4 → p1))) → (((p1 ∨ (p2 → p4)) → p3) ∨ ((p3 ∧ p3) ∨ (p2 ∨ p3)))) → p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69121250191614786324111146547 : ((p5 → ((True → (((((p3 ∧ ((p1 → True) → (True → p5))) ∨ (p1 ∧ (p4 → (p1 ∧ p3)))) ∨ p4) ∨ p4) ∨ p3)) ∨ (p2 → p2))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126409367402210834428325316781 : ((p1 ∧ (p3 ∨ ((p3 ∨ ((((((p1 ∧ p5) → True) ∨ p3) ∧ ((p4 ∧ p2) ∨ True)) ∨ (p5 → p1)) ∨ (True ∨ p3))) ∨ False))) → (p5 ∨ p1)) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Disjunctions on the left can always be decomposed.
          cases h9
          case inl h10 =>
            -- Conjunctions on the left can always be decomposed.
            let h11 := h10.left
            let h12 := h10.right
            -- Disjunctions on the left can always be decomposed.
            cases h11
            case inl h13 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h14 =>
                -- Conjunctions on the left can always be decomposed.
                let h15 := h14.left
                let h16 := h14.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h17 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
            case inr h18 =>
              -- Disjunctions on the left can always be decomposed.
              cases h12
              case inl h19 =>
                -- Conjunctions on the left can always be decomposed.
                let h20 := h19.left
                let h21 := h19.right
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h2
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
        case inr h24 =>
          -- Disjunctions on the left can always be decomposed.
          cases h24
          case inl h25 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
          case inr h26 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h2
    case inr h27 =>
      -- False on the left can always be used.
      apply False.elim h27



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200841039764584420306880645906 : ((True ∨ (((p2 ∨ (p5 ∧ p1)) ∨ False) → p3)) → ((False → (p5 → p2)) → (((((False ∧ p1) → (p2 ∧ (p5 ∨ p1))) ∨ False) → p5) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
theorem thm_5_vars_244280113628575945931422539148 : ((False ∧ True) ∨ ((p3 ∧ (p2 → p2)) ∨ ((p4 → (False ∨ ((p1 ∧ (p4 ∧ (p1 ∨ ((p1 → True) ∨ ((p4 ∧ False) → p2))))) ∨ True))) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



