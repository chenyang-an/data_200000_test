variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112505435922110370336406005307 : (((((((p4 ∨ (p1 → (((True → True) ∧ p2) → (((True ∨ p4) ∨ p4) ∧ p3)))) ∧ True) ∧ (p4 ∨ True)) ∧ p5) → False) → False) ∨ (True ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57296326562917236501881267065 : ((((p3 → p1) → p4) ∨ (p3 → (p5 ∧ (((p3 → ((False ∧ p2) ∨ False)) ∨ (((p5 ∨ p5) ∨ ((p2 → p3) ∧ p1)) ∧ False)) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57868654506852135251342543417 : (((p1 ∨ (False ∧ p1)) → (((p4 → p3) → (p3 → p3)) ∧ (((((p4 ∧ p2) → p1) ∨ ((p3 → p1) → p1)) → (p5 ∨ p4)) ∨ p1))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175851397502327594951913504044 : ((((((((p3 → p1) ∧ p3) ∨ p1) ∨ p3) ∧ p2) ∨ (p3 ∨ p2)) ∨ True) ∧ (((True → (False → p3)) ∧ False) → (p1 → (True → (True ∧ p3))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_937811863210382572228154005318 : ((((True ∨ (((p2 → p5) ∨ p1) ∨ p5)) ∧ (((p4 ∧ (p2 → p5)) ∨ ((p3 ∨ p5) ∨ (p3 → ((p5 → (p3 → True)) ∨ p3)))) → False)) → p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : ((p4 ∧ (p2 → p5)) ∨ ((p3 ∨ p5) ∨ (p3 → ((p5 → (p3 → True)) ∨ p3)))) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h11 : ((p4 ∧ (p2 → p5)) ∨ ((p3 ∨ p5) ∨ (p3 → ((p5 → (p3 → True)) ∨ p3)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h12
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h12
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h13 := h3 h11
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h15 : ((p4 ∧ (p2 → p5)) ∨ ((p3 ∨ p5) ∨ (p3 → ((p5 → (p3 → True)) ∨ p3)))) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h16
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h17 := h3 h15
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h19 : ((p4 ∧ (p2 → p5)) ∨ ((p3 ∨ p5) ∨ (p3 → ((p5 → (p3 → True)) ∨ p3)))) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h18
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h20 := h3 h19
      -- False on the left can always be used.
      apply False.elim h20
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_730326246252137784982127327891 : (((((p5 → False) → p5) → (False ∨ (((p5 ∨ ((p5 ∨ False) ∧ (p5 ∧ p5))) → p3) ∨ (((p5 ∨ p2) ∨ ((p5 ∨ p5) ∨ p2)) ∨ True)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117162290338254972195647253513 : ((True ∧ ((True ∧ ((((p2 ∨ p1) → (((p5 ∧ (p3 → (False ∧ p5))) → p4) ∨ (p5 ∧ p4))) → p2) ∨ (p2 ∨ p2))) ∨ True)) ∨ (False ∧ p3)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_155698060567878481199656572412 : (((p3 ∨ p5) ∨ ((((True ∧ (True ∨ p3)) ∧ p1) → ((p2 ∧ p2) ∨ p1)) ∨ ((True ∨ True) ∧ p5))) ∧ (True ∨ (p5 → (False ∧ (p2 ∨ p4))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_666034969698806187266701604228 : (((((p2 → ((((p1 → p1) ∧ p3) ∨ (True ∧ (p4 ∨ (p2 → (p3 → (True ∨ False)))))) → (p2 → p5))) → False) ∧ (p5 → (False → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179129007627132184013705483702 : ((p1 ∧ ((p4 → ((False ∨ (True → True)) ∧ True)) ∧ (p3 ∨ (p5 ∨ p3)))) ∨ (((True → (True ∨ p3)) ∧ ((p1 ∨ p3) ∧ (True ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310034970417808671768226535108 : (p2 ∨ (((p1 ∧ p1) ∧ ((p2 ∨ ((p3 → (p4 → p4)) ∨ p3)) → (False ∧ (p2 ∧ p4)))) ∨ ((((p4 ∨ False) → p5) → (p1 → p1)) ∨ p3))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739613782303357434505165109389 : ((((p5 ∧ p4) ∨ (((p3 ∧ p4) ∨ ((True ∧ ((p4 ∨ (p5 → (((p4 ∧ p3) → p3) ∧ (True ∧ False)))) ∨ p5)) ∧ p4)) ∨ (False → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342474856403881499263188758097 : (p2 → (((((True ∧ (p1 ∧ p3)) → (((False ∧ False) ∧ p1) → False)) → p5) ∨ False) ∨ ((((p2 ∧ ((True → p5) ∨ p1)) ∧ p3) → p2) ∧ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h8 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180341568228774943843686189103 : (((p4 ∨ ((True ∧ (False ∨ False)) ∨ (p1 ∨ (p4 ∧ p1)))) ∧ (p4 → p3)) → (((p5 ∨ p3) → (p3 ∧ (p3 ∧ (False ∨ p5)))) → (p1 ∨ p5))) := by
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
    have h6 : (p5 ∨ p3) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
      have h7 : p4 := by
        -- One of the premise coincides with the conclusion.
        exact h5
      -- We have shown the premise of h4, we can now drive its conclusion.
      let h8 := h4 h7
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h6
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- Disjunctions on the left can always be decomposed.
    cases h11
    case inl h12 =>
      -- False on the left can always be used.
      apply False.elim h12
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Conjunctions on the left can always be decomposed.
      let h16 := h15.left
      let h17 := h15.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h21
      case inr h22 =>
        -- Conjunctions on the left can always be decomposed.
        let h23 := h22.left
        let h24 := h22.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233676406729833018160926567759 : ((p2 ∨ (False → False)) → ((((((p3 ∧ p5) ∨ p5) ∨ ((p2 ∧ p2) ∨ p4)) ∨ (p1 ∨ False)) ∨ p5) ∨ ((True → ((p5 → True) ∧ p5)) → p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h2
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_731275596402653597801980294387 : ((((p4 ∨ (False ∧ p1)) → (True ∧ (((p3 ∨ (p2 ∨ ((p1 → p5) ∧ p5))) ∧ (p1 ∨ ((p1 ∨ p3) ∨ p3))) ∨ (True ∧ (True ∨ p2))))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
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
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50015270378400789642542948495 : (((((p3 ∧ p1) ∧ (p3 ∧ (p2 → p5))) ∨ ((((p1 ∧ False) ∨ p2) → ((p4 → p4) ∨ p5)) → p3)) ∧ ((False ∨ (p2 ∧ p2)) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159217158373886525361503086206 : ((p2 → (p1 ∧ (False ∨ ((False ∧ (False ∨ p5)) ∨ ((False ∨ (False ∨ (False → (p2 ∨ True)))) ∧ True))))) ∨ (False → (p4 ∨ (False ∨ (p5 → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_766666598524714940091174037 : (((p3 ∨ p2) ∧ (p3 ∧ (p4 ∧ ((p1 ∨ ((p1 ∨ p4) ∧ (((((p5 ∨ (p1 → False)) ∨ False) → p1) → False) ∨ p2))) ∨ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_892913526199432100508982893784 : ((((((p3 → (((p1 ∨ ((p5 ∧ p4) → p5)) → p1) ∨ True)) → ((p5 → False) ∧ p3)) ∨ ((p4 ∨ p5) ∨ p2)) ∧ ((p4 ∨ True) → False)) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p4 ∨ True) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h10 : (p4 ∨ True) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h11 := h3 h10
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
        have h13 : (p4 ∨ True) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h3, we can now drive its conclusion.
        let h14 := h3 h13
        -- False on the left can always be used.
        apply False.elim h14
    case inr h15 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h16 : (p4 ∨ True) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h17 := h3 h16
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774907431801051216269696544954 : (((False ∨ ((p4 ∧ (p5 → (p5 → p3))) → ((p4 ∨ ((False → (p5 ∧ p1)) ∧ ((p2 ∧ (p3 → p2)) ∧ p1))) ∧ (p1 ∨ (p1 ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733018973723858098151567802606 : ((((p2 ∧ p4) ∧ (p3 ∧ ((True ∧ (True → ((p4 ∧ False) ∧ False))) → (False ∧ (p4 → (True ∧ ((p3 ∧ p5) ∨ ((True ∧ p5) ∨ p4)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_302610545868001792305976987462 : (False ∨ (p1 ∨ (p5 → ((p2 ∧ ((p5 ∨ (False → (p4 ∨ ((True ∧ False) ∧ (p5 ∧ ((p1 ∧ p1) ∧ p1)))))) ∨ p1)) → ((p3 ∧ p1) ∨ True))))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_597528603960355939965423734628 : (((((p1 ∨ (p4 ∨ (False ∨ p1))) ∨ (((False ∨ (p2 → p2)) ∧ (p3 → p1)) ∧ (p3 ∧ (False ∨ ((p2 → p1) → (p5 ∧ p4)))))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_615206653278062731339853646583 : ((((((p2 ∧ p4) ∨ (True ∨ ((((p1 ∨ p3) → (p1 ∨ p4)) ∨ (p5 ∨ p3)) → p3))) ∧ (p2 → (((p4 ∨ p3) ∧ True) ∨ p4))) ∨ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53352325173740147056499153380 : (((((((True ∨ (False ∨ p1)) → (True → p1)) ∧ p2) ∨ p2) ∨ p1) → ((p3 → p1) → ((((True → p2) ∨ p4) ∧ (True ∨ p5)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_697920417107005020222483661997 : ((((((p3 ∨ p3) ∧ (p2 ∨ ((p4 ∨ (True → True)) → p2))) ∧ p4) ∨ ((p1 ∨ ((p2 ∧ (p4 ∨ (p5 ∨ p5))) ∨ (p1 ∧ p2))) ∨ True)) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_741167740468495980369157700902 : ((((p4 ∨ p1) ∨ (p5 ∧ (((p1 ∨ (p2 ∨ ((p2 ∧ (p3 ∨ ((p3 ∧ ((False → p1) → (True → True))) → True))) ∧ False))) ∨ p2) → p5))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39244239384171723817671087339 : (((False ∧ (((p2 ∧ True) ∨ (((((p5 → p1) ∨ p3) ∨ ((p2 ∧ p1) ∨ p1)) ∨ p1) → (p4 → ((p2 ∧ p2) ∧ False)))) → False)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_784700285954556158184028636311 : (((p3 ∨ (p4 ∨ ((False ∨ ((p3 → p4) → (p5 ∧ p3))) → (((((p1 → p3) ∨ p5) ∨ (p5 → (True ∧ p4))) ∨ p1) ∨ (p4 → p3))))) ∨ p2) ∧ True) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (p3 → p4) := by
      -- Implications on the right can always be decomposed.
      intro h6
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h7 := h3 h5
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305802286523573999719833478243 : (p1 ∨ (((True ∧ (p4 ∨ (p3 ∧ p1))) ∨ (p5 ∧ True)) → (((True → (((p1 ∧ True) ∨ p2) ∧ True)) → ((p1 → p2) → (p3 → p2))) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h6, we can now drive its conclusion.
      let h10 := h6 h9
      -- We need to get the left conjuct of h10 based on <expert-advice>.
      let h11 := h10.left
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h15 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h13
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h16 := h7 h15
        -- One of the premise coincides with the conclusion.
        exact h16
      case inr h17 =>
        -- One of the premise coincides with the conclusion.
        exact h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Implications on the right can always be decomposed.
      intro h23
      -- We want to use the implication h22 based on <expert-advice>. So we show its premise.
      have h24 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h20
      -- We have shown the premise of h22, we can now drive its conclusion.
      let h25 := h22 h24
      -- One of the premise coincides with the conclusion.
      exact h25
  case inr h26 =>
    -- Conjunctions on the left can always be decomposed.
    let h27 := h26.left
    let h28 := h26.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h29
    -- Implications on the right can always be decomposed.
    intro h30
    -- Implications on the right can always be decomposed.
    intro h31
    -- We want to use the implication h29 based on <expert-advice>. So we show its premise.
    have h32 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h29, we can now drive its conclusion.
    let h33 := h29 h32
    -- We need to get the left conjuct of h33 based on <expert-advice>.
    let h34 := h33.left
    -- Disjunctions on the left can always be decomposed.
    cases h34
    case inl h35 =>
      -- Conjunctions on the left can always be decomposed.
      let h36 := h35.left
      let h37 := h35.right
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h38 : p1 := by
        -- One of the premise coincides with the conclusion.
        exact h36
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h39 := h30 h38
      -- One of the premise coincides with the conclusion.
      exact h39
    case inr h40 =>
      -- One of the premise coincides with the conclusion.
      exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304006452940289370036762638544 : (p1 ∨ (((p3 ∨ p5) → (p5 ∨ (((p3 ∨ False) ∨ ((False ∨ p3) ∨ (False → (False ∧ False)))) → (p4 ∨ ((False ∨ (True ∨ p1)) ∧ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172652639239382529759077177532 : (((p4 ∨ p1) ∧ (p3 ∧ (((p4 ∨ (p3 ∧ (True ∨ p3))) → (p5 → p4)) ∨ False))) ∨ ((True ∧ True) ∨ ((p4 → p3) → ((p3 ∨ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247304058019935859473343181365 : ((False ∨ False) ∨ ((False ∧ ((True ∧ p5) → ((((p1 ∧ (p3 ∧ ((p1 ∨ False) ∧ p5))) ∨ p4) ∧ p5) ∨ True))) ∨ ((p1 ∨ (p3 → True)) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_178883831355135500690398971569 : (((p3 ∧ p5) ∧ ((False ∧ True) ∨ ((False ∨ (p2 → p3)) → (True ∧ p5)))) ∨ ((p1 ∨ (((p4 ∨ True) ∨ (True ∧ (p2 ∨ p1))) ∨ p1)) ∨ p4)) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111641880794047744661480730068 : ((((((p2 → ((p2 → p3) ∨ p1)) ∨ p4) → ((True ∧ True) ∧ (p2 ∨ (p4 → ((False ∨ p3) ∧ (p5 ∧ p4)))))) ∨ p1) ∨ p3) ∨ (False → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308564802563431690007078524983 : (p2 ∨ (((p1 ∨ ((p5 ∨ (p3 → False)) ∨ p4)) ∨ (p4 → (p4 ∨ ((p3 ∧ ((False ∨ p3) ∨ p5)) → (((False ∨ p4) → p3) → p1))))) ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_663943127786460678859779726286 : ((((p4 ∧ (((p3 ∧ (p4 ∨ p1)) → p5) ∧ (((((True → (p2 ∧ (False ∨ p4))) ∨ p3) ∨ (p4 ∧ p2)) → True) ∧ p3))) → (p5 ∨ False)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h8 : (p3 ∧ (p4 ∨ p1)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h7
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h9 := h4 h8
  -- One of the premise coincides with the conclusion.
  exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191569282685378083659603492930 : ((p2 ∧ (((p2 ∧ p5) ∨ (False ∨ (p4 ∨ p1))) ∨ p1)) ∨ (p2 → (p5 → (((p3 → p3) ∨ p4) ∧ ((((p1 → p4) ∨ p1) ∨ True) → True))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64209616230812180944942486409 : ((False ∨ (p2 ∧ (p3 ∨ (((((p3 ∨ (((False → (p4 ∨ (False → p3))) ∧ True) ∧ p2)) → ((p5 → True) ∨ p4)) ∨ True) ∧ False) ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602225151842285278256045959667 : ((((p5 ∧ (p4 ∨ ((((((False ∧ (p5 → False)) ∨ (False ∨ (p5 ∨ True))) → p5) ∧ ((False ∨ p3) → p3)) ∨ (p5 ∧ p3)) ∨ True))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179118028208250967316420574676 : ((p1 ∧ ((((p1 ∧ False) ∧ p3) ∧ ((p5 ∨ p4) ∨ (p5 ∨ True))) ∧ p5)) ∨ ((p3 ∧ p5) → (True ∧ (((p2 → p3) ∧ p3) ∧ (p1 ∨ p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134017805998563522251744573979 : ((((((((p1 → p5) → (((((p5 → False) ∨ p4) → p5) ∨ p3) ∧ False)) ∨ p5) ∨ (p4 ∨ p2)) ∧ p4) ∨ p5) ∨ True) ∨ (p4 ∧ (p1 ∧ p2))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351667107903454912405253994185 : (p4 → (((p5 → (p3 ∨ ((p2 ∧ ((p5 ∧ False) → p3)) ∨ (p5 ∨ True)))) → (p1 ∧ p1)) → (p5 ∨ ((((p1 ∨ False) → p4) → p3) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135340395731984262033254862838 : ((((p3 ∧ False) ∨ ((p3 ∧ ((p4 ∧ p5) ∧ (False ∨ ((p5 ∧ p2) → (p2 → False))))) ∧ p2)) ∧ ((True ∧ p2) → p1)) ∨ (p1 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51261602556346740528236074995 : ((((p2 → p1) ∨ (((p1 ∨ ((p2 → (p3 → False)) → False)) → (p4 ∨ (False ∧ p5))) ∧ p4)) ∨ ((False ∧ p2) → ((True → True) ∧ p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113675687474919679978194883419 : (((((p5 ∨ True) → ((p1 → (p3 → p1)) → (p4 → ((((p3 → True) ∧ (p5 → p2)) ∧ True) ∨ p4)))) ∨ p4) → (p3 → p5)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172538705432701162991202962481 : ((((p1 ∧ p3) ∧ False) ∨ (((((True ∧ (p1 → True)) → p4) → p3) → p2) → p1)) ∨ ((((p5 ∨ (True → p4)) ∧ (p4 → False)) ∧ p2) → p5)) := by
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
  cases h4
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : p4 := by
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h9 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h10 := h7 h9
      -- One of the premise coincides with the conclusion.
      exact h10
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h11 := h5 h8
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241657962657829122802933607393 : ((False → p5) ∧ ((p3 ∨ ((p3 ∨ ((p1 → p3) → (((p3 → True) ∨ p3) ∧ (p2 ∧ p4)))) → p5)) ∨ ((False → p3) ∧ ((True ∨ p2) → True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_309398395266340196285838006096 : (p2 ∨ ((p3 ∨ (((((p3 ∨ (((p5 ∨ (p3 ∧ (p1 ∨ p5))) → p3) ∧ p1)) ∨ p2) ∨ p3) → (p2 → p4)) → (p2 → p4))) ∨ (p4 → p3))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (((p3 ∨ (((p5 ∨ (p3 ∧ (p1 ∨ p5))) → p3) ∧ p1)) ∨ p2) ∨ p3) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638440356865374005280932039250 : (((((p4 → (((p2 ∨ p1) → True) ∧ p2)) ∧ (p3 ∧ ((p2 ∨ p1) → ((True → (((p5 ∨ (p2 ∨ p3)) ∧ p3) ∨ p4)) ∧ False)))) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_675916598027806806135693513810 : (((((p3 → ((p5 ∨ False) ∧ (p2 ∧ (p3 → (True ∨ p1))))) ∧ (p5 → ((True → (True ∧ p1)) ∧ p3))) ∧ ((p3 ∧ p3) ∨ (p5 ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47341618424753350963060957035 : ((((p3 ∨ p3) ∧ (((p4 ∨ False) ∨ (p2 → (False ∧ True))) ∨ (p3 ∧ (False → (((p4 ∧ p3) ∧ (p2 → p4)) ∨ p4))))) ∨ (p4 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_601296848898594240914812184678 : ((((p2 ∧ (((False → (p2 ∧ ((p3 ∧ True) ∨ p2))) ∧ False) ∧ ((True → ((p3 ∧ False) ∨ ((p1 ∧ p3) ∧ True))) ∧ (p5 → p2)))) ∧ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65891579349051004881420224332 : ((p4 ∨ (True ∧ ((p1 ∨ (p3 ∧ (p3 ∧ p4))) ∨ ((p1 ∨ (((False ∨ (p1 ∧ False)) → p3) ∨ (((p5 ∧ p5) ∨ p2) → p2))) → p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45945204805430678570083749922 : (((p5 → ((((((p3 → (False ∨ p3)) → (((p5 ∨ p1) ∨ p4) ∧ (p3 ∧ False))) ∨ p2) → p5) → (p4 ∨ True)) ∧ (True ∨ False))) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149825748336099419155612781125 : ((p1 ∨ (((((p1 ∨ p1) → p4) ∧ (False ∨ (p3 → ((True → p1) ∨ False)))) → (p2 ∨ p1)) ∧ (p3 ∨ p1))) ∨ (p2 → (p2 ∨ (False → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708662302594039216725661396765 : ((((((p4 ∨ ((p1 → p5) → p3)) ∧ p1) → p3) → (p2 ∧ (True → (p3 ∧ (((p3 ∨ p3) ∨ False) → ((True → p5) → (p4 ∧ p3))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200992705850560610630910919849 : ((p3 ∨ ((p5 ∧ ((p2 ∧ p5) ∨ True)) → True)) → ((False ∧ ((False ∧ (p1 ∧ (True ∨ p5))) ∨ (True ∨ (((p2 ∧ p3) → p4) ∨ True)))) ∨ True)) := by
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
theorem thm_5_vars_134384524827347818982088424558 : (((p4 ∨ (p3 ∧ (((p1 ∨ p2) → (p2 ∧ p1)) ∧ ((p3 ∨ ((((True ∧ p2) → p5) ∨ p2) ∨ p3)) ∨ False)))) ∨ p4) ∨ ((p1 → True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182633681734213585139902617931 : (((p4 ∨ (p4 → ((p1 → p4) ∨ p1))) ∨ ((p4 ∨ p3) → True)) ∧ (((p5 ∨ p4) ∧ (p4 ∨ p4)) → (p2 ∨ (True ∧ (False → (p3 → True)))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h7
      -- Implications on the right can always be decomposed.
      intro h8
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h10
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h14
      -- Implications on the right can always be decomposed.
      intro h15
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Implications on the right can always be decomposed.
      intro h18
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135872915949931970353253802965 : (((((True ∧ False) → p4) ∧ ((p4 → ((p3 ∧ p3) ∨ p2)) ∧ p3)) ∨ (((True ∧ p5) → False) ∧ (False → (p3 ∧ p1)))) ∨ (False → (False ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147019607250484077861288592966 : ((((True ∨ ((p1 → ((((p2 ∧ p4) ∧ p2) → (p2 ∨ (p4 ∧ False))) → p3)) ∨ p3)) → (p3 → p4)) ∧ True) ∨ (p4 → (False → (p3 ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_598927732129050105574723135611 : (((((False ∨ p2) ∧ ((((True ∧ p5) → False) ∧ p2) ∨ ((((False ∨ (p2 ∨ (((True ∧ p4) → False) ∨ p1))) ∨ p4) → False) ∧ False))) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_714680857100112707395656989518 : (((((p3 ∨ True) → (p5 ∧ (p4 → p3))) → (p5 ∧ ((p4 ∨ (((p4 → p1) → p5) ∨ (False → (p5 → p3)))) ∨ ((p3 → False) ∧ p1)))) ∨ p2) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- One of the premise coincides with the conclusion.
  exact h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612772201939734414291793126495 : (((((((True → p1) → p2) ∨ (False ∨ (((((p3 ∧ False) ∨ p2) ∨ p1) ∨ (False → False)) ∧ (True → (p2 ∧ True))))) ∨ (True ∧ p4)) ∨ True) ∨ False) ∧ True) := by
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
theorem thm_5_vars_228027108351474130524161055104 : ((p3 ∧ (p3 → p2)) ∨ (p2 ∨ ((((p3 → p2) → ((p1 → (p5 ∧ (p5 ∧ ((True ∧ (p2 ∨ p3)) → True)))) ∧ False)) ∨ p3) ∨ (p4 → True)))) := by
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
theorem thm_5_vars_702307113366943411313426844817 : (((((p5 ∨ (((p4 → p4) → True) ∨ (p2 ∨ p1))) ∧ p3) ∨ (((False ∨ ((p2 ∧ (p1 ∨ True)) ∨ p3)) → True) → ((True → p4) ∧ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118099097547910294636358838136 : ((False ∨ ((((p4 ∧ (((p3 ∨ ((((p4 ∧ ((p2 ∧ p3) → p2)) ∨ p3) → p4) → p4)) ∨ p5) → p4)) ∧ False) ∧ p3) ∨ True)) ∨ (False ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61266090159267012225481700089 : ((False ∧ (p1 ∨ (((p5 → p2) ∧ p3) ∧ ((p1 ∧ ((p1 ∧ (((p5 → p4) ∧ ((True ∧ p4) ∧ (p1 ∧ p3))) → True)) ∨ p2)) ∨ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40903438429136490570095439051 : (((((p4 → False) → ((False ∨ ((p4 → False) → (((False → ((False → p3) ∧ False)) ∧ p5) ∨ (p5 ∨ p1)))) ∧ p1)) ∧ (False → p2)) ∨ True) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181251609169059337330185495397 : ((p3 ∧ (p4 → (p4 → ((p5 → p5) ∨ ((True → p5) ∨ (p1 ∨ p5)))))) → ((p5 ∧ ((True ∨ (p4 ∧ p4)) → p4)) ∨ (p3 → (p3 ∨ False)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172310432391049347749037482505 : (((True ∧ (p3 → (False ∨ (p3 ∧ (p1 → True))))) → (p2 ∧ ((p5 ∧ p2) → p3))) ∨ ((p4 ∨ ((True ∨ p4) ∧ p1)) ∨ (p3 → (True → True)))) := by
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
theorem thm_5_vars_185209064979737588554040616058 : ((True ∧ (p5 ∧ (p3 ∧ ((True → p3) ∨ (p3 → (p5 ∨ True)))))) ∨ ((p1 ∧ False) ∨ ((False ∧ (True ∨ (False ∨ (p5 → (p3 ∧ p5))))) → p4))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232018926058103524877257832272 : (((p3 ∨ True) → p2) → (((((p4 → True) → (p4 ∨ ((False → p1) ∨ (False → (p1 ∧ p5))))) ∧ ((p3 ∨ (p4 ∨ p1)) ∨ True)) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149056352171641408374149397065 : (((p5 → (p2 ∨ False)) ∨ ((p1 ∨ (p2 ∨ ((((True ∧ (p1 → p5)) ∧ p1) ∧ p4) ∧ False))) ∨ (p1 → p1))) ∨ ((p1 ∧ (p1 ∨ p3)) ∧ True)) := by
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
theorem thm_5_vars_308541181367366710123132659829 : (p2 ∨ ((((p1 → (p3 → (p5 → p5))) ∨ (p4 → (p1 ∨ p5))) ∧ (((((p2 ∨ p3) ∧ p1) ∨ p1) ∧ False) ∨ ((False → p1) ∨ True))) ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60613908205032411954826558016 : ((True ∧ (((((p4 ∨ False) ∧ ((p1 ∨ p4) ∨ (p5 ∨ (False → True)))) ∧ (True ∧ p2)) → (p1 ∨ ((p1 ∨ True) → p5))) ∨ (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158662527210212848203803288779 : ((p1 ∧ (True → (((((p1 → p1) → p5) ∨ p2) ∧ p1) → (False ∧ (p1 → (p4 ∨ (p2 ∧ p3))))))) ∨ ((False ∧ (p4 → False)) → (p1 ∨ p2))) := by
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
theorem thm_5_vars_94199109415793571641717785172 : ((p2 ∧ ((((((((False ∨ (True → (p4 ∨ (p4 ∧ (p2 ∧ ((p5 ∨ p4) → True)))))) ∨ p2) ∧ p1) ∨ True) → False) ∧ p5) ∨ p2) → p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((((((False ∨ (True → (p4 ∨ (p4 ∧ (p2 ∧ ((p5 ∨ p4) → True)))))) ∨ p2) ∧ p1) ∨ True) → False) ∧ p5) ∨ p2) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607728622290685874369724956868 : (((((False ∨ (False ∧ (((p4 ∧ (True → p4)) ∧ p4) ∨ ((False ∧ (((p4 ∧ True) ∧ ((p2 ∧ p3) → True)) ∧ p3)) → p2)))) ∧ p4) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_59597821632745137545401180136 : (((p4 → p3) ∨ (((p4 ∧ ((((p1 ∧ (p3 ∧ (((p5 → p1) ∧ (p1 ∧ p1)) ∧ (False → p5)))) ∨ p4) → p2) → p2)) → p3) ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37409766607723180676360297264 : ((((((p5 → (p4 → (True → (p1 ∨ p1)))) ∨ ((p3 → False) → ((p1 ∨ ((p3 ∧ p5) ∨ p3)) ∨ p4))) ∨ (True ∨ p4)) ∨ p5) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191894477088358664460148657141 : ((p5 ∨ ((p3 ∧ (p4 ∨ (False ∧ (True → p4)))) ∨ True)) ∨ (((p5 ∧ False) ∧ (((False → ((False ∨ p2) ∨ p4)) → p3) → p2)) ∧ (p5 ∨ p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_658621614037661030658506141495 : ((((p3 ∨ (((p1 ∨ (False ∧ p3)) → p1) → (p3 ∨ (((True ∨ p2) ∨ (p3 ∧ p1)) ∧ (((p5 → False) → False) ∨ False))))) ∨ (True ∨ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234651723211379626616712336275 : ((p3 → (p5 → p3)) → ((True ∧ ((p2 ∨ p2) → False)) ∨ ((((p1 ∧ p1) → (p5 → (p5 ∧ p5))) ∧ p3) ∨ (True ∨ (p2 ∧ (p1 ∧ p4)))))) := by
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
theorem thm_5_vars_631499432780425359667432143228 : ((((((((((True → True) ∧ (p5 ∧ ((p3 ∨ True) → (True ∨ p1)))) ∨ p4) → (p1 ∧ p2)) ∨ p3) ∧ ((p5 ∧ p1) ∧ p2)) → p3) → p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60126728639662445948138003619 : (((p4 ∨ True) → ((p5 ∨ ((((True → (((True ∧ True) ∧ p5) ∧ p1)) → True) ∧ p1) ∧ ((p2 ∧ (p3 → True)) ∧ (p5 ∧ p1)))) ∨ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200335824522701548451862390070 : (((p2 ∨ p2) ∧ ((p3 ∨ p2) ∧ (True → False))) → ((True → p3) ∧ (p3 ∧ (p3 ∧ ((True ∧ (True ∧ p2)) ∧ (False → ((True ∧ p3) ∨ p1))))))) := by
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
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h11 := h7 h10
      -- False on the left can always be used.
      apply False.elim h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h4.left
    let h14 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- We want to use the implication h14 based on <expert-advice>. So we show its premise.
      have h17 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h14, we can now drive its conclusion.
      let h18 := h14 h17
      -- False on the left can always be used.
      apply False.elim h18
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h19 := h1.left
  let h20 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h19
  case inl h21 =>
    -- Conjunctions on the left can always be decomposed.
    let h22 := h20.left
    let h23 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h22
    case inl h24 =>
      -- One of the premise coincides with the conclusion.
      exact h24
    case inr h25 =>
      -- We want to use the implication h23 based on <expert-advice>. So we show its premise.
      have h26 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h23, we can now drive its conclusion.
      let h27 := h23 h26
      -- False on the left can always be used.
      apply False.elim h27
  case inr h28 =>
    -- Conjunctions on the left can always be decomposed.
    let h29 := h20.left
    let h30 := h20.right
    -- Disjunctions on the left can always be decomposed.
    cases h29
    case inl h31 =>
      -- One of the premise coincides with the conclusion.
      exact h31
    case inr h32 =>
      -- We want to use the implication h30 based on <expert-advice>. So we show its premise.
      have h33 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h30, we can now drive its conclusion.
      let h34 := h30 h33
      -- False on the left can always be used.
      apply False.elim h34
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h35 := h1.left
  let h36 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h35
  case inl h37 =>
    -- Conjunctions on the left can always be decomposed.
    let h38 := h36.left
    let h39 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h38
    case inl h40 =>
      -- One of the premise coincides with the conclusion.
      exact h40
    case inr h41 =>
      -- We want to use the implication h39 based on <expert-advice>. So we show its premise.
      have h42 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h39, we can now drive its conclusion.
      let h43 := h39 h42
      -- False on the left can always be used.
      apply False.elim h43
  case inr h44 =>
    -- Conjunctions on the left can always be decomposed.
    let h45 := h36.left
    let h46 := h36.right
    -- Disjunctions on the left can always be decomposed.
    cases h45
    case inl h47 =>
      -- One of the premise coincides with the conclusion.
      exact h47
    case inr h48 =>
      -- We want to use the implication h46 based on <expert-advice>. So we show its premise.
      have h49 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h46, we can now drive its conclusion.
      let h50 := h46 h49
      -- False on the left can always be used.
      apply False.elim h50
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h51 := h1.left
  let h52 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h51
  case inl h53 =>
    -- Conjunctions on the left can always be decomposed.
    let h54 := h52.left
    let h55 := h52.right
    -- Disjunctions on the left can always be decomposed.
    cases h54
    case inl h56 =>
      -- One of the premise coincides with the conclusion.
      exact h53
    case inr h57 =>
      -- One of the premise coincides with the conclusion.
      exact h57
  case inr h58 =>
    -- Conjunctions on the left can always be decomposed.
    let h59 := h52.left
    let h60 := h52.right
    -- Disjunctions on the left can always be decomposed.
    cases h59
    case inl h61 =>
      -- One of the premise coincides with the conclusion.
      exact h58
    case inr h62 =>
      -- One of the premise coincides with the conclusion.
      exact h62
  -- Implications on the right can always be decomposed.
  intro h63
  -- False on the left can always be used.
  apply False.elim h63



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61556878844643186850311023607 : ((p1 ∧ (((p3 ∨ p1) ∨ ((p5 ∨ p2) ∨ (False ∨ p5))) ∨ (p5 ∨ ((p4 ∧ False) ∧ (p4 ∧ ((p3 → (p1 ∧ False)) ∨ (p1 ∨ p4))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_909189512371576490561986849902 : (((((p5 → (p5 → ((p1 ∨ p2) → p4))) ∧ (p4 ∧ (True ∨ (p4 → ((p1 ∧ False) ∧ p2))))) ∧ (((p2 ∨ p5) → (p2 → False)) ∨ p2)) → p4) ∧ True) := by
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
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h10 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h12 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h13 =>
      -- One of the premise coincides with the conclusion.
      exact h6
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171720703397251487195949343230 : (((((p5 ∧ (p2 ∧ ((p3 ∨ (p4 ∧ False)) → p3))) → (True ∨ p4)) ∧ p1) → p5) ∨ ((p1 ∧ ((p4 → (p3 ∧ (p2 ∧ False))) ∨ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_330586277690364521256580969159 : (True → (p5 ∨ (p5 ∨ (((True ∨ p4) → (False ∨ False)) → ((((p1 → p3) ∧ (True ∨ p1)) → p1) ∨ ((p5 ∧ False) ∨ (p4 ∧ (p1 ∧ p3)))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (True ∨ p4) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113757159110342964320766603648 : (((((p1 → (p4 ∧ (p3 ∨ p3))) ∨ (p1 ∨ True)) ∨ (((((p2 → False) ∧ (p5 ∨ p1)) ∧ p2) ∧ p1) ∨ False)) → (p1 ∧ p2)) ∨ (p5 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40561958322909108010748110540 : ((((p3 → (((True ∧ True) → (((((p3 → (p4 → p5)) ∨ p2) ∨ p1) → p2) ∨ ((True ∧ (True → p1)) ∨ p1))) ∧ p4)) ∨ False) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720449747181507915659325107107 : (((((p4 ∧ (p1 ∧ p1)) ∨ p3) → (p1 ∨ ((p5 ∧ p5) ∨ ((p3 → (((p5 ∨ True) → p4) ∨ (p5 ∧ (p4 ∨ p1)))) → (False ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47492799274805599219371078032 : (((False ∨ (p4 ∨ (((((p3 ∨ p1) ∨ p5) ∧ False) ∧ (p5 → ((p4 ∨ ((p4 → p4) ∨ p2)) ∨ (p1 ∧ p5)))) ∧ p5))) ∨ (True ∨ False)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703819725916121764245344004992 : ((((((((p4 ∧ p1) ∨ p2) ∧ (p3 → p3)) ∨ p1) ∨ p5) → ((p4 ∧ ((p4 ∨ ((p3 → p5) ∧ ((p3 ∧ False) ∧ p5))) → p2)) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40829594113444934381954618927 : ((((False → (True → ((p3 ∧ p5) → ((False → p2) ∨ (False ∨ ((False ∧ (p4 ∧ p5)) → ((True ∧ (p1 ∨ False)) ∧ p2))))))) → p2) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322324838854647179305809612957 : (p5 ∨ (((p1 → (False ∨ (((p2 → p4) ∨ (p2 → (p4 ∧ (False ∧ p4)))) ∧ (p1 ∧ (True → (True ∨ (p3 ∧ p4))))))) ∧ (p5 ∧ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



