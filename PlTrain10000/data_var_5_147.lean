variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156797644534441833135863808831 : (((p4 ∧ ((p2 ∧ True) ∧ ((((p1 → p2) ∧ (p3 ∨ (p2 ∧ (False ∨ True)))) ∨ p3) ∧ True))) ∧ p3) ∨ (((True ∨ (p3 ∨ p3)) → False) → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∨ (p3 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134366921135843614396445284032 : (((p1 ∨ (p2 → ((p3 ∧ (p2 ∧ (p5 ∨ (((p5 ∨ p1) ∨ p5) ∨ ((p4 ∧ p1) → p2))))) ∨ (True ∨ p1)))) ∨ p3) ∨ ((p5 ∨ p5) → False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186605212711360644588075143840 : (((((p4 ∧ (p5 ∧ p1)) → p3) ∨ (p2 ∨ True)) → (p5 ∧ False)) → ((p2 ∧ ((p2 ∨ (True ∧ (p3 ∨ p1))) ∨ (False ∨ (p5 ∨ p2)))) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ (p5 ∧ p1)) → p3) ∨ (p2 ∨ True)) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : (((p4 ∧ (p5 ∧ p1)) → p3) ∨ (p2 ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218076660142660022651953234145 : (((p5 ∨ p2) ∧ (False ∨ p1)) → (((p4 → (True ∨ ((p4 ∨ (p5 ∨ False)) ∨ p1))) ∧ ((p4 ∧ p3) ∨ ((False → (p2 ∧ p3)) ∧ p5))) ∨ True)) := by
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
      -- False on the left can always be used.
      apply False.elim h5
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232290717810748188440113545878 : (((p2 → p5) → p4) → (((p5 ∧ (((p3 ∨ True) ∧ p4) ∧ (False ∨ ((p1 ∨ p2) → p1)))) → False) → (p3 ∨ ((p5 ∧ (True → p1)) → p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∧ (((p3 ∨ True) ∧ p4) ∧ (False ∨ ((p1 ∨ p2) → p1)))) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h9 : (p2 → p5) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h11 := h1 h9
    -- One of the premise coincides with the conclusion.
    exact h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h12
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h15 := h2 h8
  -- False on the left can always be used.
  apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669008521042899270217393341086 : ((((((p5 ∧ (p5 ∨ (p3 → (p2 ∧ ((((p5 → p5) → p3) ∧ ((p5 ∨ False) ∧ p3)) → p5))))) ∧ p1) → p4) ∨ (True → (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115684138538583351140100022177 : (((False ∨ (((p4 → p1) → False) → p3)) ∨ (((p5 ∧ True) ∨ (p2 ∨ (p3 ∨ p5))) ∨ ((p2 ∧ ((True ∨ p3) → p3)) ∨ True))) ∨ (p2 ∨ p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158979586019761991296323543724 : ((p3 ∨ (((p2 → (p4 → (False → ((p4 → p3) → (p4 ∧ p2))))) ∧ p2) ∨ ((p1 ∧ p5) ∧ p1))) ∨ (True ∨ (((p2 ∨ p3) ∨ False) → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180509781416789815657792209140 : (((p3 ∨ ((False ∧ p5) ∨ (p3 ∧ (p2 → p4)))) ∧ (p3 ∧ (p3 ∨ True))) → (p4 ∨ (p1 ∨ (((True ∨ (p1 → False)) ∨ (False ∧ p2)) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h9
    case inl h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h11
    case inr h13 =>
      -- Conjunctions on the left can always be decomposed.
      let h14 := h13.left
      let h15 := h13.right
      -- Conjunctions on the left can always be decomposed.
      let h16 := h3.left
      let h17 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52549161986469253082062740011 : (((((p1 → (p3 ∧ (((True → p3) ∨ p5) → p3))) ∨ (p2 ∧ p3)) → p4) ∨ (((p1 ∨ (p5 → p3)) ∧ (p4 ∨ p5)) ∨ (p3 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114028427877839720444187357853 : (((((((p5 → (p1 ∨ p1)) ∧ ((True ∨ p4) ∨ ((p1 → False) ∧ (p3 ∨ p1)))) → False) → p2) → p4) ∨ ((p2 → False) ∨ True)) ∨ (p2 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118698703927236594791679944510 : ((p5 ∨ ((p1 ∨ ((((((p2 ∧ True) ∧ (p3 ∧ p1)) ∧ p1) ∧ (True ∨ ((p1 → (True ∧ p2)) ∧ p4))) ∧ False) ∨ p2)) ∨ p2)) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118167426412148880499389110880 : ((False ∨ ((p3 ∧ False) ∨ (p5 → ((p3 ∨ (p1 → (((True ∨ p2) → (((p2 ∧ (p5 → True)) ∨ p1) → p3)) ∧ p3))) ∨ False)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39885594950685428212454641469 : (((p2 → ((p5 ∧ (False → (p1 → (p3 → False)))) ∧ ((((p5 ∧ ((True ∨ p4) ∧ False)) ∨ p5) ∧ (p1 ∨ p5)) ∨ (p4 ∧ p3)))) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_590009245638389825247332195548 : (((((((((False ∨ p2) ∨ p3) ∧ (False ∧ ((p1 ∧ True) ∨ p4))) → (p1 ∨ p2)) ∨ (p1 → (((p4 ∧ p3) ∨ p4) ∧ p2))) → p2) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177634311140156329569943766311 : ((((((p5 → p4) ∨ (p5 ∨ False)) ∨ ((p2 → True) → False)) ∧ True) ∧ p3) ∨ (((p2 ∨ p4) ∨ ((p2 ∨ (p3 ∧ (p1 → p4))) ∨ p2)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54060369629672723177316484331 : (((((False → p5) ∨ False) ∧ (((p5 ∨ p5) ∨ p3) ∧ p5)) → ((((p3 → p5) ∨ p5) → (((p4 ∨ p4) ∨ p1) ∨ (p2 → p5))) ∨ p5)) ∨ p1) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h3.left
    let h6 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113535239391114941131417147515 : ((((p1 ∨ (False ∨ (p4 → (p1 ∧ True)))) → ((True → ((False ∨ p3) → (p5 ∧ p4))) ∧ (p3 → (p4 → p1)))) ∨ (p5 ∧ p4)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40072070912365380197611589813 : (((((p3 → ((((((((p4 → (p1 ∧ (p1 ∨ p4))) ∨ (p1 → p2)) ∨ False) ∨ p2) → False) ∧ p3) ∧ False) ∧ p1)) ∨ True) ∧ p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690871507487984470198716753679 : (((((((((((p4 → p5) ∧ True) ∧ p1) ∧ p2) ∧ True) ∨ p3) ∨ True) ∧ (p2 → p5)) → ((p3 ∨ (False ∧ (p4 ∧ p4))) → (p2 ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351005834750499844918469903350 : (p4 → ((p3 ∨ (((p3 ∧ p1) → ((p1 ∧ p2) → (((False ∧ p5) ∨ ((p2 ∨ (True ∨ p4)) ∧ False)) → p3))) → (False ∨ p5))) ∨ (p2 ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135748463478975482696360038189 : (((((True ∨ p4) ∧ True) → ((p5 ∧ ((False ∧ (True → p5)) ∨ p5)) ∨ p5)) ∨ ((False ∧ p2) → (p1 → (False ∧ p4)))) ∨ (p5 ∨ (p1 ∨ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- False on the left can always be used.
  apply False.elim h3
  -- Conjunctions on the left can always be decomposed.
  let h5 := h1.left
  let h6 := h1.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207990397588381854662232607348 : ((((True ∨ p3) ∨ False) ∨ (False → p2)) → (((p1 → (p1 ∧ p2)) → True) ∧ ((False ∧ (p3 ∨ ((p2 ∨ p3) → (p1 ∨ p3)))) ∨ (p1 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h6
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h8
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_733465605582732647559810797103 : ((((p4 ∧ p2) ∧ ((((p1 → (((((p5 ∨ p3) → p2) ∧ p2) ∨ False) ∨ (p3 ∨ (p4 → True)))) ∨ False) ∧ (p3 → (p3 → p2))) ∨ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68019430154131724977623119005 : ((p2 → (True ∧ (p5 → (((p3 ∨ (False ∧ False)) ∧ (p4 ∧ (p4 ∨ p2))) ∨ ((True ∨ ((p2 ∨ p4) ∧ (p2 ∨ (p3 → p4)))) ∨ p3))))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335893747811265430830798482191 : (p1 → ((((p4 ∨ True) → (p1 ∧ False)) → ((p2 ∧ p4) ∨ (((p3 ∨ (p2 ∨ p2)) → ((True ∨ ((p1 ∨ False) ∧ p1)) ∧ p4)) ∨ p4))) ∧ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_140523379220663575074266075466 : (((p5 ∨ ((p3 ∧ ((p2 ∨ p5) ∨ p1)) ∧ ((p2 → (True ∧ p5)) ∧ (p2 ∨ p5)))) ∧ (p4 ∨ (p2 ∨ (True ∧ p4)))) → ((p3 → p5) ∨ p4)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h8
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
  case inr h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h13.left
    let h16 := h13.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h14.left
        let h20 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h20
        case inl h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h22
          case inr h23 =>
            -- Disjunctions on the left can always be decomposed.
            cases h23
            case inl h24 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Implications on the right can always be decomposed.
              intro h25
              -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
              have h26 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h24
              -- We have shown the premise of h19, we can now drive its conclusion.
              let h27 := h19 h26
              -- We need to get the right conjuct of h27 based on <expert-advice>.
              let h28 := h27.right
              -- One of the premise coincides with the conclusion.
              exact h28
            case inr h29 =>
              -- Conjunctions on the left can always be decomposed.
              let h30 := h29.left
              let h31 := h29.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h31
        case inr h32 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h33 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h33
          case inr h34 =>
            -- Disjunctions on the left can always be decomposed.
            cases h34
            case inl h35 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Implications on the right can always be decomposed.
              intro h36
              -- One of the premise coincides with the conclusion.
              exact h32
            case inr h37 =>
              -- Conjunctions on the left can always be decomposed.
              let h38 := h37.left
              let h39 := h37.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h39
      case inr h40 =>
        -- Conjunctions on the left can always be decomposed.
        let h41 := h14.left
        let h42 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h42
        case inl h43 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h44 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h44
          case inr h45 =>
            -- Disjunctions on the left can always be decomposed.
            cases h45
            case inl h46 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Implications on the right can always be decomposed.
              intro h47
              -- One of the premise coincides with the conclusion.
              exact h40
            case inr h48 =>
              -- Conjunctions on the left can always be decomposed.
              let h49 := h48.left
              let h50 := h48.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h50
        case inr h51 =>
          -- Disjunctions on the left can always be decomposed.
          cases h3
          case inl h52 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h52
          case inr h53 =>
            -- Disjunctions on the left can always be decomposed.
            cases h53
            case inl h54 =>
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- Implications on the right can always be decomposed.
              intro h55
              -- One of the premise coincides with the conclusion.
              exact h51
            case inr h56 =>
              -- Conjunctions on the left can always be decomposed.
              let h57 := h56.left
              let h58 := h56.right
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h58
    case inr h59 =>
      -- Conjunctions on the left can always be decomposed.
      let h60 := h14.left
      let h61 := h14.right
      -- Disjunctions on the left can always be decomposed.
      cases h61
      case inl h62 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h63 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h63
        case inr h64 =>
          -- Disjunctions on the left can always be decomposed.
          cases h64
          case inl h65 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h66
            -- We want to use the implication h60 based on <expert-advice>. So we show its premise.
            have h67 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h65
            -- We have shown the premise of h60, we can now drive its conclusion.
            let h68 := h60 h67
            -- We need to get the right conjuct of h68 based on <expert-advice>.
            let h69 := h68.right
            -- One of the premise coincides with the conclusion.
            exact h69
          case inr h70 =>
            -- Conjunctions on the left can always be decomposed.
            let h71 := h70.left
            let h72 := h70.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h72
      case inr h73 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h74 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h74
        case inr h75 =>
          -- Disjunctions on the left can always be decomposed.
          cases h75
          case inl h76 =>
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- Implications on the right can always be decomposed.
            intro h77
            -- One of the premise coincides with the conclusion.
            exact h73
          case inr h78 =>
            -- Conjunctions on the left can always be decomposed.
            let h79 := h78.left
            let h80 := h78.right
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h80



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_879555747678841040426759411439 : ((((True → ((((p1 → p1) ∨ p1) → ((True ∧ (p2 ∧ (p1 ∧ p3))) ∧ ((p5 → p4) ∨ (p2 ∧ (False → p4))))) ∧ p5)) ∧ (p1 ∨ p4)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the right conjuct of h10 based on <expert-advice>.
    let h11 := h10.right
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41876031159591208942267020605 : ((((False ∧ (p5 → p3)) ∨ (((p1 → (p5 → ((p5 ∧ (p2 ∧ p2)) ∨ (p3 → ((p4 ∨ (p3 ∧ True)) → False))))) → False) ∧ p3)) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42370464463188242559626400434 : (((p4 ∧ ((p2 ∧ (p4 ∧ ((p5 → (p2 ∧ p2)) → (p2 ∧ (p1 ∨ ((p5 ∨ p4) ∧ ((p5 → (False ∧ False)) → p1))))))) ∧ True)) ∨ True) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313086836557659763888351454631 : (p3 ∨ ((((p3 ∨ p1) ∨ ((p5 → (p5 ∨ (p2 ∧ ((p4 ∨ (p4 ∨ p1)) → p1)))) ∧ ((p2 ∧ (p2 ∨ True)) ∨ True))) ∨ (p3 ∧ True)) ∨ False)) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_478028905025267080717815159024 : (((((True ∨ p5) ∨ ((p3 ∧ p5) → (True ∨ (True ∨ p4)))) → (((p5 ∨ p5) ∨ p3) ∨ ((True → (p3 → p2)) ∨ (p4 → (p5 → True))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187139812654124323074967675754 : (((p4 ∨ p3) ∨ (((p3 ∧ (p5 ∨ p3)) → p5) ∧ (p5 ∨ p3))) → ((((p5 ∨ (p1 ∧ ((p4 → p5) ∨ p2))) ∨ p2) → p4) ∨ (True ∨ p5))) := by
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
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_721906029408538436799093746199 : ((((p5 ∨ ((p2 ∨ p1) ∨ False)) → (p1 ∧ ((((p4 ∧ ((False ∧ False) ∨ p2)) ∧ p4) ∧ (p4 → (p3 → (p3 ∧ (p1 → p3))))) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37520932284864230333174502879 : ((((True ∧ ((((p5 → (True ∧ p5)) ∨ False) → (p2 → (p5 → (p1 ∨ ((p2 ∧ p4) ∨ (False → p5)))))) ∧ (False ∨ p4))) ∨ p3) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804577084646426875618734637822 : (((p3 → ((p5 ∨ (((p2 → p2) → p5) ∨ True)) → (p2 → (((((True ∧ (True ∧ p1)) ∨ p2) ∨ ((p5 ∧ False) ∨ p5)) ∨ p2) ∧ p1)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244737002008491388339296069983 : ((p1 ∧ False) ∨ (((p5 ∧ ((True ∨ p4) ∨ p2)) → (((p2 → (False ∨ (p5 ∨ ((p3 ∧ True) ∧ p4)))) ∨ p3) ∨ ((False → p5) ∧ False))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337773207074841017326990848875 : (p1 → (((False ∧ p1) ∧ (((p4 ∧ p3) ∧ ((True → ((p4 ∧ p1) → False)) ∨ p4)) → p2)) ∨ (((((p4 ∧ False) ∧ p2) ∨ p3) ∧ p3) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47912130078869189647449237533 : ((((((True ∧ p3) ∧ (True ∧ ((False ∨ False) → False))) ∧ (p3 ∧ (p4 ∨ (p2 ∧ ((False ∧ p3) ∧ False))))) → (p4 ∧ p4)) → (p2 ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_657696289460476003335717229747 : (((((p1 → p3) → ((((p3 ∧ (True ∧ (False → ((p1 ∧ False) ∨ p5)))) ∧ p2) → False) ∨ (False ∧ (p5 → (False ∧ p3))))) ∨ (p2 ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310633763873272445454569617554 : (p2 ∨ ((p1 ∧ ((False ∨ p2) ∨ p2)) ∨ ((((p4 ∨ (((True ∨ (True ∨ (p4 ∨ False))) ∨ True) → (True ∨ p5))) ∨ True) → (p1 ∨ p1)) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_639641813170311594856446039359 : (((((p3 ∧ (p3 → p2)) ∧ (((p1 → True) ∧ ((((True ∨ p5) → ((p3 ∧ (p1 → p2)) → p1)) ∨ p3) ∨ (False → True))) → p4)) → p2) ∨ p4) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- One of the premise coincides with the conclusion.
  exact h7
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194232224348473719126732799681 : ((p4 → ((p1 → (p1 ∧ (p5 ∧ (p5 ∧ p4)))) ∨ p5)) → ((True ∧ ((p4 ∨ (False ∧ p3)) ∧ (p1 ∨ ((p5 → False) ∧ p3)))) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248986532954633493296841351163 : ((p4 ∨ False) ∨ (((((False → (((p3 ∨ (False → True)) ∨ (p5 → False)) ∧ p4)) → p1) ∧ (False ∨ (True ∧ (p1 ∨ p4)))) ∨ (False → False)) ∨ p4)) := by
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
theorem thm_5_vars_217768932872620498388258824088 : (((p5 ∧ (p3 ∨ p4)) → p5) → ((((((((p2 ∨ p5) ∧ p2) ∨ p1) ∧ p4) ∨ p1) → p1) ∧ (False ∧ (p1 ∨ (True → p5)))) ∨ (True ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161221192597745972279572442577 : (((p4 → p5) ∨ ((((p3 ∨ (p1 ∧ p5)) ∨ p5) ∧ ((p2 ∧ p2) ∨ ((p1 ∧ True) ∧ p4))) → p2)) → ((True → (p3 → (p1 ∧ p5))) ∨ True)) := by
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
theorem thm_5_vars_137727955658825409146075046214 : ((p1 ∨ (p4 ∧ (((False → ((p3 → p3) → (p3 → p2))) → ((p1 → p3) ∧ ((p4 ∨ (True → p5)) → p5))) ∧ p1))) ∨ (p3 → (True ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45539850715632062956909565375 : (((p1 ∨ (p5 → (((p4 ∧ (p2 ∨ (p1 ∧ p2))) ∨ (((p3 ∧ ((False → (p2 ∨ p5)) ∨ False)) ∨ p4) ∧ p1)) ∨ (False ∨ p1)))) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66574923629295821668282050088 : ((True → (((((p4 → False) → p2) → (((p2 ∨ p1) ∨ (((p2 ∧ p2) ∨ p4) ∨ p2)) ∧ (p5 ∨ p1))) ∧ (p5 → p4)) → (False ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_231927616892555490334332702705 : (((False ∨ p4) → False) → ((((True → (p5 ∧ p3)) ∨ (p4 ∧ (((p4 → p4) ∧ False) ∨ p5))) ∨ True) ∨ (((p2 ∨ p2) ∨ p1) → (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122769239846272665989704178585 : (((p4 ∨ (((False ∨ (p2 → (p2 ∨ ((p5 → (p1 → ((p4 ∨ p1) ∧ False))) ∧ (p2 → False))))) ∧ True) ∧ True)) → (True → False)) → (p4 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p4 ∨ (((False ∨ (p2 → (p2 ∨ ((p5 → (p1 → ((p4 ∨ p1) ∧ False))) ∧ (p2 → False))))) ∧ True) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- False on the left can always be used.
  apply False.elim h6
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : (p4 ∨ (((False ∨ (p2 → (p2 ∨ ((p5 → (p1 → ((p4 ∨ p1) ∧ False))) ∧ (p2 → False))))) ∧ True) ∧ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h8
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64090820083488072327479628098 : ((False ∨ ((((False → (((p2 ∨ p4) → True) ∨ p4)) ∧ (p4 ∨ p2)) ∨ p3) → ((p3 ∨ (p5 ∧ ((p5 → p4) ∨ (True ∧ p1)))) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54375729640375125895930455207 : (((p1 → (p5 ∧ ((p1 ∨ p3) → (p4 ∨ p3)))) ∧ ((p5 ∨ ((((p5 ∨ p4) → True) → (False ∧ p1)) ∧ ((False ∨ True) → True))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307139319891721834375751598863 : (p1 ∨ (False ∨ ((((((True → (p1 ∨ False)) ∧ (False → p3)) ∨ False) ∧ (p5 → (False ∨ p4))) ∧ p2) ∨ ((p2 ∧ False) → (p3 ∨ (p5 ∨ p2)))))) := by
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346324210292779959125078124712 : (p3 → ((((p4 ∧ ((p1 ∧ ((True ∨ p3) ∨ False)) ∧ ((False ∨ False) ∨ ((p2 ∨ False) ∨ True)))) ∧ True) ∨ ((p3 ∨ p2) → True)) ∨ (p5 → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46914645943264269552727979038 : (((((p3 ∧ (((p5 ∧ ((p3 → p1) ∧ p2)) ∨ p3) ∧ False)) ∨ (True ∨ ((False ∧ (p2 ∨ p3)) ∨ (True ∨ p1)))) ∨ p2) ∨ (p2 → p3)) ∨ p5) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245910524051143194097120784864 : ((p3 ∧ p5) ∨ ((p4 → ((False → (p4 ∨ (p3 ∨ (((p5 ∨ p2) ∨ p1) ∨ True)))) → p5)) ∨ (p2 → (((p4 ∧ p4) ∨ (p5 ∨ p2)) ∧ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_198088016665923220136827551905 : (((p5 ∨ p2) ∨ (p1 ∧ ((p4 ∨ p2) ∧ p1))) ∨ ((p4 → False) → ((((p4 ∧ ((p3 → p1) → p3)) ∧ (p4 → p5)) ∧ p5) → (p3 ∧ p5)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h10 := h1 h9
  -- False on the left can always be used.
  apply False.elim h10
  -- Conjunctions on the left can always be decomposed.
  let h11 := h2.left
  let h12 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h13 := h11.left
  let h14 := h11.right
  -- Conjunctions on the left can always be decomposed.
  let h15 := h13.left
  let h16 := h13.right
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_636297131190382674722525238542 : (((((((p1 ∧ ((((p5 → p2) ∨ p2) ∧ p3) → (p4 ∨ (p4 ∧ p5)))) → False) ∨ p5) → (p3 → (p5 → (p3 ∨ (False → True))))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_327330377372965230843130137919 : (True → ((((p1 → (p3 → (((p4 → False) ∨ ((p4 ∧ (p3 → (p5 ∨ p4))) ∧ p3)) → (p1 ∧ (p5 ∨ (p5 ∨ p5)))))) ∨ True) → False) → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((p1 → (p3 → (((p4 → False) ∨ ((p4 ∧ (p3 → (p5 ∨ p4))) ∧ p3)) → (p1 ∧ (p5 ∨ (p5 ∨ p5)))))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164608477423344255647074550334 : (((p1 ∧ ((((True → p3) → ((p5 → p3) → (False → False))) ∨ p3) → (p4 ∨ p2))) ∧ p3) ∨ ((p2 ∧ False) ∨ (((p1 ∧ p4) ∨ p1) → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    exact h3
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111931620927947130877099848775 : ((((p3 ∨ (p5 ∨ (p4 ∨ (False ∧ ((p2 → False) → p5))))) ∧ (((p4 → p2) ∧ (p5 → True)) → ((p2 ∧ p2) ∧ False))) ∨ p3) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263069288665804884641701823486 : (True ∧ (((((True → (p3 ∧ (p4 ∨ ((p2 ∨ (p5 → p4)) → True)))) → ((False ∨ False) ∧ True)) ∨ (p5 ∧ (p2 → p2))) ∧ True) ∨ (p5 ∨ True))) := by
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
theorem thm_5_vars_329156581217428499738506887075 : (True → ((((False ∨ p4) ∨ True) → False) → (p3 ∨ ((True → (p5 ∨ ((False → (p5 ∨ (p4 ∨ p4))) ∧ False))) ∧ (p5 ∧ (p5 → (False → p1))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : ((False ∨ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158631766382731111819676979358 : ((p1 ∧ ((True → ((((p1 ∧ p5) → True) → ((p3 → (True → p2)) → p4)) ∨ (True ∨ True))) ∧ p2)) ∨ ((p4 ∨ (p4 ∧ (p4 ∨ p2))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357488922662958515394797718088 : (p5 → (True ∧ (((p3 ∧ (p2 ∨ (((p2 ∨ p2) → p1) ∨ p1))) → ((p2 ∧ (True ∧ (p3 ∨ (False → (p5 ∨ False))))) ∧ (True → False))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147866243809654287001651761473 : (((p2 → (((p3 ∨ p1) ∧ (((False ∧ p3) ∨ p3) ∨ (p3 ∨ p3))) → (True ∨ ((p3 → p2) ∧ p3)))) → p3) ∨ (False → ((p3 ∨ p1) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168542561966230484270697638872 : ((p1 ∧ ((True → ((p5 → p5) → (True ∨ (((p4 ∨ p4) → (p3 ∧ p5)) ∧ False)))) → p5)) → (p3 ∨ ((p1 ∨ True) ∧ ((p3 → p2) → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_67757576542309595361150403157 : ((p2 → (((((True → p3) ∧ (((True → (p5 ∨ (p5 ∧ p1))) → p3) ∧ ((p3 → p1) ∧ True))) → (p2 ∧ False)) ∧ (p5 → True)) ∨ p2)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_226008115649447165762196490562 : (((p4 ∧ p1) ∨ p2) ∨ (((p5 → (p5 ∨ p3)) → (p3 → ((False ∧ p5) → p4))) ∧ (((p2 → True) → (False ∧ (p1 → p5))) → (p3 ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  apply False.elim h4
  -- Implications on the right can always be decomposed.
  intro h6
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58638482637549931788661136469 : (((p1 → False) ∧ ((p5 → ((((p4 ∧ True) ∧ p1) → (p5 → p4)) ∧ p2)) → (((True ∧ p5) → ((True → False) ∧ (p2 → True))) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111957473782563015208400855017 : ((((False ∨ (((False → p2) ∨ p1) → (False ∨ p2))) ∨ (p5 → (((p4 ∨ (p1 → p3)) → p2) ∨ ((p2 → p5) → p2)))) ∨ True) ∨ (p5 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116447817720933891174250677605 : (((p5 → (p5 ∨ False)) → (((p3 ∧ ((p5 → p4) ∨ False)) ∧ False) ∧ (((p2 → ((p5 ∧ p1) ∧ (p4 ∧ True))) ∨ p3) → p1))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260311909572672685129417150966 : ((p2 → p4) → ((True ∨ (p2 ∧ True)) ∧ (p5 → (((False ∨ (p1 ∨ (False ∨ True))) ∨ p2) ∧ ((((p4 ∧ (p1 ∧ True)) ∨ p1) ∨ p5) ∨ p4))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_265573474794393255728202036170 : (True ∧ (p1 ∨ (((((p3 → (p5 → p3)) ∧ (p3 → ((((p3 → p3) ∧ p4) → p4) ∨ p5))) → (p3 ∨ (p4 ∧ p2))) → (False ∧ True)) ∨ True))) := by
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
theorem thm_5_vars_171348442755949057056093219066 : (((((p1 ∨ True) → ((False → (False ∧ (p3 → (False ∧ p4)))) → p1)) → False) ∧ False) ∨ ((True ∧ (p1 ∨ p2)) → (((p2 ∧ p2) ∨ p1) ∨ True))) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43779962132660541863425543480 : ((((p1 ∨ ((((p5 → (p5 → (True ∧ p5))) ∧ ((p4 ∨ False) ∨ (((True → True) ∧ p5) ∧ (p3 ∧ p2)))) ∧ p2) ∧ p3)) → p1) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178909745037921574422548523182 : (((p5 ∨ p3) ∧ (((p5 → True) → (p2 ∧ ((p2 ∨ p3) ∧ True))) ∧ p5)) ∨ ((p2 ∨ ((p2 ∧ p2) ∨ (p2 → False))) → ((p1 ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247519700627822751162137087721 : ((False ∨ p3) ∨ (p3 → ((p4 ∧ (p1 → p4)) ∨ ((((p5 ∨ (((p1 → ((p4 ∨ p2) → (p2 → True))) ∨ p5) ∨ p4)) → p1) ∨ True) ∨ p1)))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218562990588891875892387118542 : (((False → p3) → (p4 ∧ p5)) → ((p3 ∧ ((p1 ∧ ((((((p4 → p2) ∧ p1) ∨ p4) → (p1 ∨ True)) ∧ p3) → (p4 ∧ p1))) ∧ p3)) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_694089614588512541389888995881 : (((((p4 ∨ (p1 ∧ (True ∧ (p3 ∧ (p5 → p3))))) ∨ (p3 ∨ (False → True))) ∨ (((p3 ∧ (True ∨ p2)) → p3) ∨ ((p3 ∨ True) → True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299189584094430567357048026000 : (False ∨ (((p1 ∧ ((p3 ∨ p1) ∨ ((((((p4 → p4) ∨ ((((True ∧ p1) ∧ p4) → True) ∨ p3)) ∨ p1) → p2) → p5) ∧ p4))) → p3) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255946948466226793624316523972 : ((True ∨ p2) → (True ∧ (p3 → (p3 ∧ (((False → p3) ∧ ((((False → (True ∨ False)) → ((p5 ∨ (True ∧ p4)) ∧ p3)) ∨ p1) ∨ p5)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215516672089538489348572763673 : ((p4 ∧ (False ∧ (p1 ∨ p3))) ∨ (p5 → ((p5 → ((True ∨ p5) ∧ p4)) → (p2 → ((p2 ∧ (((True ∨ p3) ∧ p5) ∨ p3)) ∧ (p4 ∧ p5)))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52707956564957906559495080551 : (((p5 → (((p5 → False) ∨ (p4 ∧ p2)) → (False ∧ (False ∧ (True ∧ p3))))) ∨ ((p3 → (p5 → p4)) ∨ ((False ∧ (p3 → p5)) ∨ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177481337946178458150933860473 : ((p1 → (((((p3 ∧ p2) ∧ (p1 → (True → p5))) ∧ False) ∧ False) ∨ True)) ∧ (((p4 → p3) → ((((False ∧ p2) ∧ p4) ∧ p3) ∨ p1)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214793976420663979016976677946 : (((p1 ∨ p3) ∨ (p1 ∨ p2)) ∨ (False ∨ ((False → p1) → ((((False → False) → p5) ∨ (((False → True) → p4) ∨ (p1 ∧ p3))) → (True → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655686551009037389034926041722 : ((((((p1 → (p2 ∧ ((p1 ∧ True) ∨ p2))) → (((p1 → (p4 ∧ p4)) ∧ False) ∧ (False ∧ False))) ∧ ((p5 ∨ p5) ∧ True)) ∨ (p5 → p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197424228760731181087453386070 : (((p4 → (True ∨ ((p5 ∧ p4) → p4))) → p4) ∨ (((p2 ∧ (p5 → ((False ∧ (((p3 → False) ∧ p1) ∨ p1)) ∧ True))) ∧ False) → (False → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129399327558281700743566827124 : (((False ∨ ((p3 ∧ p5) ∨ ((((((p1 ∧ p1) → p2) ∨ True) ∧ (True ∧ (p4 ∨ (p2 ∨ p5)))) ∨ False) ∨ True))) ∨ p4) ∧ ((p1 → True) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247895199676424364375887820510 : ((p1 ∨ p3) ∨ (((p4 ∨ (True ∨ p1)) → (p1 ∨ ((p1 → (((p3 ∧ (False → (p2 ∧ p3))) ∨ True) ∧ p2)) ∨ ((p1 → p3) → p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357080295473617260590623972324 : (p5 → (((p2 → p4) ∨ p5) → ((((False ∨ ((((p2 ∧ p4) → p5) → (True → p1)) ∨ (p4 ∧ p2))) ∨ (p5 → (p4 → p4))) ∧ True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_683603823588298639991183107882 : ((((((p2 ∨ ((((p1 → p2) ∧ p3) ∧ ((p5 → p1) → (True ∨ p4))) ∧ True)) → p3) ∧ p4) ∨ ((p5 → ((p2 ∨ False) ∧ p3)) ∨ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_319410394830502629215676914134 : (p4 ∨ ((False ∨ ((False → ((p2 ∨ p3) → ((p3 → (p2 ∨ False)) → p3))) → False)) → (((p5 ∨ p4) → (p3 ∨ ((p5 ∧ p4) → False))) ∨ p5))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (False → ((p2 ∨ p3) → ((p3 → (p2 ∨ False)) → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Implications on the right can always be decomposed.
      intro h7
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h8 =>
        -- False on the left can always be used.
        apply False.elim h5
      case inr h9 =>
        -- False on the left can always be used.
        apply False.elim h5
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h10 := h3 h4
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704824383642509375887333917729 : ((((False ∨ (((p4 ∧ (p4 ∧ p1)) → (p2 ∨ p5)) ∨ False)) → (False ∨ ((p1 ∨ p5) → (p1 ∨ (p5 → ((p2 ∧ p5) ∨ (p2 ∧ p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178422271250447121473169849745 : (((False → (((p5 ∧ p2) ∨ ((p3 → True) ∨ False)) ∧ p1)) → (p1 ∨ p1)) ∨ (((((p1 → p1) → p3) ∨ True) → (True ∨ (p3 → p5))) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157850689550530124892759149703 : (((((p2 ∨ (p3 → True)) → p4) ∨ (p1 ∨ (p2 ∨ p4))) ∧ (((p5 ∨ (False → p5)) ∧ True) ∧ p4)) ∨ ((p1 ∨ p4) → (p3 ∨ (p4 ∨ p1)))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135954403406551818879392924700 : ((((True ∨ p1) ∧ ((p3 → (False ∧ p4)) ∨ (p2 ∧ False))) ∧ ((((p4 ∨ (p2 ∨ p5)) ∧ p5) ∧ False) ∨ (p1 ∨ p1))) ∨ (p2 → (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_805034305787837792750132682955 : (((p3 → ((p5 → p2) → (((((p2 ∧ p2) ∨ p3) ∨ (p3 → False)) ∧ p5) ∧ (((False ∨ (p1 → (True ∨ True))) ∧ p1) ∨ (p2 ∨ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142302593513007808471480989638 : ((p2 ∧ (p3 → (((p3 ∨ (p3 ∧ ((True ∧ p3) ∧ (p4 ∧ True)))) → ((p4 ∧ p5) ∧ (p2 ∨ p5))) ∨ (p2 ∧ p5)))) → (True ∧ (p5 ∨ True))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



