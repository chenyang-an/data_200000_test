variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193692828173946671213920989533 : ((p1 ∧ ((p3 ∧ p3) ∨ ((True ∨ p4) ∧ (p1 ∨ p1)))) → (False ∨ ((((p5 ∧ True) ∧ ((p5 ∧ (False → p2)) → p5)) ∧ (True ∨ False)) ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h14 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148522797461065249143889027549 : (((((p4 ∧ p1) ∨ (((True ∧ True) → False) → p5)) ∨ (p1 ∨ True)) → (p2 → (p3 ∨ (p1 ∧ (p3 ∨ p2))))) ∨ (False → ((True ∨ p4) ∧ p5))) := by
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
theorem thm_5_vars_190416317994063588929252053387 : (((False ∨ (p5 ∨ (((p4 → p2) → False) ∨ p4))) ∨ False) ∨ (((p3 ∨ (p3 ∨ (False ∧ p1))) ∧ ((((p5 → p3) ∧ False) ∧ p2) ∨ p4)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_192563224616300644269972015172 : (((p2 ∨ ((((False → True) ∧ p3) → p4) ∨ p1)) ∨ p3) → (((False → ((True ∨ (False ∨ p1)) ∧ True)) → p3) → (p2 ∨ (True → (p1 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
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
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h8
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h11
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53966773943124911264203188339 : (((((p3 → p1) ∧ (((True → p2) ∧ p1) → p2)) ∧ p4) → (p4 ∧ ((p3 ∨ ((p3 ∧ False) → ((p5 ∧ False) → (p2 ∧ p4)))) → p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_591854625406393076545216278586 : (((((((p4 → p5) ∨ (False ∨ (False ∨ (((p1 ∧ p1) ∧ p4) ∧ False)))) ∧ (p2 ∧ ((p4 ∨ p4) ∨ (p5 ∧ True)))) ∨ (p2 ∧ p4)) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_171318490568462202389532386219 : ((((((p3 ∧ ((p1 ∧ p4) ∧ (p3 → p4))) → (False → p2)) → p5) ∨ p4) ∧ p3) ∨ ((True ∨ p3) → (p3 → (((p2 ∧ p1) ∨ p3) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h7 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h10 =>
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h11 =>
      -- One of the premise coincides with the conclusion.
      exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_209298520980193271107851608445 : ((True → (False ∧ (p4 ∨ (p5 → p2)))) → (((((((True ∧ True) ∨ (p4 → p3)) → p4) ∧ p5) ∧ True) ∨ (True ∨ (p3 ∧ p5))) ∧ (p3 ∧ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the left conjuct of h3 based on <expert-advice>.
  let h4 := h3.left
  -- False on the left can always be used.
  apply False.elim h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h5 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h5
  -- We need to get the left conjuct of h6 based on <expert-advice>.
  let h7 := h6.left
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49503507650087199709967029168 : ((((p2 ∨ (p1 ∧ (p5 ∧ ((p2 ∨ ((p5 ∧ (p1 → (False → (p1 ∨ p5)))) ∧ False)) ∨ (p5 ∨ p5))))) → False) → ((True ∧ True) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157812633169370707618970495002 : (((((p3 → (p3 ∨ (p4 → False))) → (True → (False → p4))) → p5) → ((p1 ∨ p4) → (p4 ∧ p3))) ∨ (p5 → (p1 → (p5 → (p5 ∨ p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48441477044744298502280315281 : (((p4 → (p2 → (p1 ∧ ((((((p5 ∨ p2) ∧ True) ∨ p2) → (True → (p1 → p5))) ∧ p3) → (True ∧ (p5 ∨ p5)))))) → (p2 → p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322269007052051733220304054787 : (p5 ∨ (((p1 ∨ (((p5 → (p2 → p4)) ∧ ((p1 ∨ (False → p1)) ∨ ((True ∧ True) → False))) → (p2 ∨ (p5 ∧ (p5 ∧ p1))))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185747502741058582360819167831 : ((p3 → (p2 ∧ ((((p1 ∧ p3) → False) ∧ (p4 ∨ False)) ∨ p5))) ∨ ((p5 ∨ (p3 ∨ True)) → ((p5 ∨ p4) ∨ (p1 ∨ ((False ∧ p4) → p4))))) := by
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
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h5
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- False on the left can always be used.
      apply False.elim h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137280939073771543984453436129 : ((p2 ∧ (((p1 ∨ ((p3 ∨ (((p3 → p4) ∧ True) ∧ ((True → p5) → p5))) ∨ (True → (p1 ∨ True)))) → p3) ∧ p5)) ∨ (p2 ∨ (True ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116351067561847870623381588068 : ((((p2 ∨ p3) ∨ p5) → ((True → (False ∧ ((p2 ∨ ((False ∧ p5) ∧ p5)) → (False → ((False ∨ p5) ∧ p4))))) → (p2 ∧ False))) ∨ (True ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the left conjuct of h7 based on <expert-advice>.
      let h8 := h7.left
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h11 := h2 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h15 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h16 := h2 h15
      -- We need to get the left conjuct of h16 based on <expert-advice>.
      let h17 := h16.left
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h19 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h20 := h2 h19
      -- We need to get the left conjuct of h20 based on <expert-advice>.
      let h21 := h20.left
      -- False on the left can always be used.
      apply False.elim h21
  case inr h22 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h23 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h24 := h2 h23
    -- We need to get the left conjuct of h24 based on <expert-advice>.
    let h25 := h24.left
    -- False on the left can always be used.
    apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259098873872236615830556133943 : ((True → p5) → (((p3 ∨ True) → False) → (p3 ∨ (p3 ∧ ((p4 ∧ (((p5 ∨ (p1 → p5)) ∧ (True → p3)) → p5)) ∨ (p4 ∨ (p5 ∨ p3))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p3 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136861868560005555879186853878 : (((p5 ∧ p4) ∨ (True → ((p2 ∧ (p1 → (p2 ∨ (((p3 → (True ∨ (p3 → p2))) ∨ True) ∧ (p1 ∧ p2))))) → p4))) ∨ ((p4 ∨ True) ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314285875074675719179774679467 : (p3 ∨ ((p4 → (p1 ∧ (True → (p1 ∨ ((((False → p2) → (p1 → ((True ∨ (p5 → p1)) ∨ p4))) → p5) ∨ p5))))) ∨ ((p2 ∧ p5) → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_156608867628807963476529398354 : (((((p1 ∨ True) → ((((True ∧ p3) ∧ p3) ∨ (p4 → (True ∧ True))) ∨ (p2 → False))) ∧ p4) ∧ p2) ∨ (True ∧ (True ∨ ((p4 → p2) ∧ True)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184137756717168066028040313402 : (((p4 ∧ ((((p1 → (True → p4)) ∧ p3) ∨ p2) → p1)) ∨ True) ∨ (((((False ∨ False) → p2) → p2) ∧ (p4 ∧ p4)) ∨ (p5 ∨ (True ∨ p3)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_679787327424274749622023200994 : ((((((p3 ∨ (p2 ∨ p1)) → (p3 ∧ (((p5 → p4) → (p4 → p4)) ∧ (False ∧ (True ∨ p3))))) ∨ p1) → ((p5 ∧ p3) ∨ (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172870210811191781633340323709 : ((p1 ∧ ((True → (p1 ∧ ((p1 ∨ p4) ∧ (((False → p2) ∧ p3) → p3)))) ∨ p3)) ∨ (p1 → ((p2 ∨ p2) → (False ∨ (False → (p4 → False)))))) := by
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52455549412733417088764549777 : (((p5 ∧ ((True ∧ ((False ∨ (p2 → p1)) ∨ (p1 ∨ p4))) → (True ∧ p3))) ∧ (((p2 ∧ p2) ∨ p1) ∨ (p2 → (p1 → (p3 ∧ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_775450511402854589456438511507 : (((False ∨ (p3 ∧ (((True ∨ (p4 → (p3 ∧ False))) ∨ ((True ∨ p5) ∨ (False ∧ ((False ∨ (p3 ∨ p5)) → True)))) ∧ ((p5 → p4) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51224823559622997722111630666 : (((((p1 → (False ∨ False)) ∧ False) ∧ (((False ∧ False) ∨ True) ∨ ((p1 ∧ p3) ∨ (p4 ∧ p5)))) ∨ (((p3 → True) ∨ False) ∨ (p3 ∧ True))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729528219442139581934902707254 : (((((p2 ∨ False) ∨ p4) → ((p4 ∨ (p4 ∨ (((((False → p3) → (p5 ∨ (False ∧ p5))) → (False ∧ p1)) ∨ (p4 ∧ p2)) ∨ p4))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177830428744544361769347694468 : ((((((p4 ∨ (p4 → p2)) ∧ (p3 ∨ (p3 ∨ p1))) ∧ p2) ∧ p2) ∨ p4) ∨ (((((True ∨ (True ∧ p3)) → p3) → p1) → p3) ∨ (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_804113044429177460336447392759 : (((p3 → (((((((True ∧ ((p1 ∨ (p4 → (True ∨ p4))) → False)) ∧ p3) → p3) ∨ p3) ∧ p1) → False) ∨ (((p5 ∨ p5) ∨ p5) ∨ True))) ∨ p1) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670800104235206524748226762047 : ((((p1 ∧ ((((p4 ∨ True) ∨ ((p5 ∧ (p3 ∨ False)) ∨ (((p4 → p1) ∨ p3) ∧ p5))) ∧ p5) ∨ (p3 ∧ p1))) ∨ (True ∨ (p4 ∧ p5))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_350947165387310538943566399547 : (p4 → ((((((False → ((p4 ∨ p2) → p4)) ∧ ((p4 → False) → ((p3 ∨ p3) → p4))) → p3) ∧ p4) ∨ (p1 ∧ (p4 ∧ p1))) ∨ (p4 ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736350448330094486903217605367 : ((((False → p5) ∧ (((((((False → p4) → p3) ∧ p5) ∨ True) ∧ ((True ∨ True) ∧ (True → True))) → p5) ∨ ((p2 ∨ True) ∨ (p3 ∨ p4)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47007390481174926583139925735 : (((((True ∧ p1) → (False ∧ ((((p3 ∨ p2) ∧ (((p5 → p2) ∧ p4) ∨ p5)) ∨ (p2 ∧ p4)) → (p5 → True)))) → p5) ∨ (p5 ∨ True)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228884737615374508977562627108 : ((p4 ∨ (p2 ∧ True)) ∨ ((p5 ∧ ((p5 ∧ ((p1 → (p5 → (p2 ∨ False))) ∧ p1)) ∨ p4)) → (((p4 ∨ ((p5 ∨ p4) → False)) ∧ p1) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
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
theorem thm_5_vars_113551951678323910884469311313 : (((((p3 → True) ∨ p2) → (((p3 → (((p4 ∨ p1) ∧ (p2 ∧ p5)) ∨ p3)) ∨ p5) ∨ ((True ∧ True) → p4))) ∨ (p1 → p1)) ∨ (True ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_16612454736499661151264100074 : ((((((p5 → ((p2 ∧ p2) ∧ p4)) ∧ ((p4 ∨ (False → (p3 ∧ True))) → (p4 → p1))) ∨ (p5 ∨ p3)) ∨ p4) ∨ (p1 ∨ (True ∨ p3))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
theorem thm_5_vars_68597057080886220332094165263 : ((p4 → ((((p5 ∨ (False ∨ (p4 → ((((p3 → ((True ∨ p1) → (True ∨ p2))) → True) ∨ False) → (p4 ∧ p5))))) ∨ p3) ∧ p2) ∨ p4)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247364423516027122500420525706 : ((False ∨ p1) ∨ ((((p5 ∨ False) ∨ (p5 ∨ ((p2 ∨ ((p2 ∧ (p1 → (p4 ∨ False))) ∧ p4)) ∧ p2))) ∨ p3) ∨ ((p2 → (p1 ∧ p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111120152821343659525718233817 : (((((True ∨ ((True ∧ p5) ∧ (True → True))) ∨ p2) ∧ ((False → (((True → False) ∧ p4) → (True ∧ (True → p2)))) → p4)) ∧ True) ∨ (p1 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197288689846099573833396242202 : (((((True ∧ p3) ∨ True) → (p4 → p1)) → p3) ∨ (p2 ∨ ((p4 ∧ (p5 → p5)) ∨ ((False ∨ (p4 ∧ p1)) ∨ (p4 ∨ ((p5 → True) ∧ True)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179353750268114294741263532178 : ((p2 ∨ ((((p3 ∨ False) ∨ (((True → p5) → p2) → p2)) ∧ p4) ∨ True)) ∨ ((((True → True) ∧ p5) → (True ∧ ((True → p3) ∧ p4))) ∨ p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_19810226162254221187983850354 : ((((((p1 ∨ (p2 ∧ False)) ∧ p3) ∨ p1) ∧ (p1 ∨ (p3 → (True ∨ (p4 → p1))))) → (p5 ∨ ((((p4 ∨ p3) ∨ p2) ∧ True) ∨ p1))) ∧ True) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h8
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h7
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h14
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h13
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54106075943173997921845171715 : (((p1 ∧ (p3 ∨ ((p2 ∧ False) → ((True ∨ p5) → p1)))) → (p3 ∧ ((p5 ∨ (p4 → (p1 → p1))) ∧ (p4 ∧ ((False → p4) → p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_2582347595274728987862254841 : (((False → (((p3 ∧ p1) → p1) → p3)) → False) → (((p4 ∧ (p2 → p5)) ∧ (p4 ∧ (p1 ∧ (p3 ∧ p5)))) ∨ ((p1 → p5) ∧ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (False → (((p3 ∧ p1) → p1) → p3)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52744359628438412889912240951 : (((((p2 ∧ False) → ((False ∨ p4) ∨ ((p4 → (p3 → p3)) → p4))) ∨ p5) → ((True → ((False ∧ p3) ∧ ((False ∧ True) ∨ p5))) → False)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We need to get the left conjuct of h5 based on <expert-advice>.
    let h6 := h5.left
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h9 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h10 := h2 h9
    -- We need to get the left conjuct of h10 based on <expert-advice>.
    let h11 := h10.left
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- False on the left can always be used.
    apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_769012123404254271294925515 : (((p1 → True) ∧ (((p1 ∨ p4) → (p2 → (((False → (False ∨ (p5 → p1))) ∧ p1) ∧ ((p5 ∨ p4) → (p4 ∧ p1))))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262403379849600087025498515352 : (True ∧ (((p5 → False) → (p1 → (p2 → ((p1 → p4) → ((False ∨ (p2 ∨ p3)) → (((p4 ∨ p2) → ((p4 ∧ p2) ∧ p4)) ∧ p2)))))) ∨ p1)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- One of the premise coincides with the conclusion.
        exact h7
      case inr h11 =>
        -- One of the premise coincides with the conclusion.
        exact h7
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h16 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h17 := h4 h16
        -- One of the premise coincides with the conclusion.
        exact h17
      case inr h18 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h19 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h20 := h4 h19
        -- One of the premise coincides with the conclusion.
        exact h20
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h21 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h22 =>
      -- False on the left can always be used.
      apply False.elim h22
    case inr h23 =>
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h25 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  case inr h26 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h27 =>
      -- False on the left can always be used.
      apply False.elim h27
    case inr h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h30 =>
        -- One of the premise coincides with the conclusion.
        exact h3
  -- Disjunctions on the left can always be decomposed.
  cases h6
  case inl h31 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h32 =>
      -- False on the left can always be used.
      apply False.elim h32
    case inr h33 =>
      -- Disjunctions on the left can always be decomposed.
      cases h33
      case inl h34 =>
        -- One of the premise coincides with the conclusion.
        exact h31
      case inr h35 =>
        -- One of the premise coincides with the conclusion.
        exact h31
  case inr h36 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h37 =>
      -- False on the left can always be used.
      apply False.elim h37
    case inr h38 =>
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h40 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h41 := h4 h40
        -- One of the premise coincides with the conclusion.
        exact h41
      case inr h42 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h43 : p1 := by
          -- One of the premise coincides with the conclusion.
          exact h2
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h44 := h4 h43
        -- One of the premise coincides with the conclusion.
        exact h44
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h45 =>
    -- False on the left can always be used.
    apply False.elim h45
  case inr h46 =>
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h48 =>
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193046170666157468623268244024 : (((p4 ∨ (p1 ∨ ((p5 ∨ p5) ∧ p2))) → (False ∧ p1)) → (p4 → ((False ∧ p4) ∨ ((p1 ∨ p2) ∨ (p2 ∨ (p4 ∧ ((p2 → p4) ∧ False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : (p4 ∨ (p1 ∨ ((p5 ∨ p5) ∧ p2))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161994458627126233232261998735 : ((p3 → (((p3 ∧ p3) → (p2 ∧ p5)) ∨ (((((p2 ∧ (False ∨ p3)) → True) → p4) ∨ False) → False))) → (((p1 → p3) → (p3 ∧ p1)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44020978644328084536916863350 : (((((p3 ∧ ((p5 ∨ True) → (True → p3))) → (p3 ∧ (((p1 → ((p4 → (True ∧ p5)) ∧ p4)) ∨ False) ∧ p3))) → (p4 → p3)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127086477894175736333976800303 : ((False ∨ (((p5 → True) → p4) ∧ (p2 → (((p3 ∧ p1) ∨ ((False ∨ False) → ((False ∨ ((p2 ∧ True) ∧ True)) → False))) ∧ False)))) → (p4 ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h8 := h4 h6
    -- One of the premise coincides with the conclusion.
    exact h8
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- We want to use the implication h11 based on <expert-advice>. So we show its premise.
    have h13 : (p5 → True) := by
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h11, we can now drive its conclusion.
    let h15 := h11 h13
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60370955769220596232514655966 : (((p3 → False) → ((p3 → (p4 ∨ p5)) ∧ (((p3 → p5) ∧ p1) ∨ (p4 ∨ (True ∨ (p4 ∨ (p5 ∧ ((p4 ∨ p2) → (p1 ∧ p4))))))))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h3
  -- False on the left can always be used.
  apply False.elim h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342669506243385645805073874035 : (p2 → ((True ∧ (((p3 ∨ p3) ∨ True) ∧ (p1 ∧ (p5 → True)))) ∨ ((((p5 ∨ (p5 ∧ p4)) ∨ False) ∨ True) ∨ (((p1 ∧ p3) ∧ False) ∧ p5)))) := by
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
theorem thm_5_vars_44317231461032452471302257077 : ((((((False → (p4 ∨ p4)) ∧ (p2 ∧ p4)) ∧ ((p1 → (p4 ∧ (p3 ∧ p3))) → p3)) ∨ (((p3 ∨ p2) ∨ (False → p2)) → p1)) → p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_759135133670054104046190847180 : (((p2 ∧ ((p1 ∧ ((p5 ∨ (p3 ∧ (((p1 → (p5 → True)) → p5) ∧ (p2 → True)))) ∧ (p3 ∧ (p3 ∧ (p3 ∧ False))))) ∧ (p2 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133252305867858530879362499925 : ((p2 → (((((((False ∨ p5) ∧ p5) ∧ p4) ∧ (((False → (p2 ∧ (p1 ∨ p4))) → p1) ∨ False)) ∧ p1) ∨ p3) ∨ p2)) ∧ (True → (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622260728651180799986371967534 : ((((p2 ∧ (p5 → (p5 ∧ ((p5 ∧ (p5 ∧ True)) ∧ ((((p2 ∧ True) ∨ (False ∧ p3)) ∨ (((True ∨ False) → p4) ∧ p2)) ∧ True))))) ∨ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55970710526070824329316513864 : (((((p2 → p1) ∨ p5) ∧ False) ∨ (((((p2 ∨ (((p2 ∨ (p5 ∧ True)) → p3) ∨ p1)) ∨ True) → p3) ∨ (p5 ∨ True)) ∨ (p5 → p1))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113963270928682799997709919639 : ((((p5 → True) → ((p1 ∨ p4) ∨ ((((p3 → (True ∨ (p2 ∨ True))) ∧ (p2 ∨ p4)) → False) ∨ p4))) ∧ ((p4 → p4) → p3)) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126378838326811629292805673036 : ((p1 ∧ ((p5 → (p5 ∧ p3)) ∧ ((p4 → p1) → ((((p5 ∨ (p5 → True)) ∨ p4) ∧ (False ∧ (p4 ∨ True))) ∧ (True ∨ p4))))) → (p2 ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (p4 → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h8 := h5 h6
  -- We need to get the left conjuct of h8 based on <expert-advice>.
  let h9 := h8.left
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- We need to get the left conjuct of h10 based on <expert-advice>.
  let h11 := h10.left
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703016197411868745915193482442 : (((((p5 → (p1 → False)) → (p3 → ((p5 ∧ p1) ∨ p1))) ∨ (p5 → (p4 ∨ (((p1 ∧ p5) ∧ (p3 ∨ (p3 → (p5 ∨ p1)))) ∨ p5)))) ∨ p2) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158198504580403052156552146161 : ((((False → p5) ∧ p1) ∧ ((p3 → False) ∧ (((p1 ∨ (p2 ∧ False)) ∨ p5) ∧ ((True ∨ p5) → False)))) ∨ ((True ∧ p1) → ((False ∧ True) → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_519080341291701808891248197998 : ((((True ∨ p2) → ((False ∨ True) ∧ ((p5 → (p5 → (p1 ∨ False))) → ((True ∧ (p2 ∧ p5)) ∨ ((p4 ∧ p3) → ((p5 → p4) ∨ p4)))))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308684977363487118160429251540 : (p2 ∨ ((p1 ∨ (((p4 ∧ (True ∨ (p4 ∨ (((((p4 → (p3 → True)) ∨ False) ∧ p5) ∧ p4) ∧ (p2 ∧ (p2 → p1)))))) → p2) ∧ False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_724139323754963457484002737381 : ((((p2 ∧ (p3 ∨ p5)) ∧ ((False → ((p3 ∧ ((False ∨ (((False ∨ (p5 ∨ p4)) ∧ (p5 ∧ p2)) ∧ (p5 ∧ p3))) ∧ False)) → p4)) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343621888137935639996248221399 : (p2 → (True ∧ ((True → (((((p2 ∨ False) → p1) ∧ p2) → (((p3 ∨ p1) → False) ∨ (p2 ∨ (((True → p1) ∧ False) → p3)))) ∨ p5)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165439231528261571507752521832 : (((True → ((p2 ∧ p1) → ((False ∨ ((p1 ∧ p1) ∨ True)) ∨ p4))) → ((p4 → p3) → p2)) ∨ (((p4 → True) ∨ p1) ∨ ((p5 → p4) ∧ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57811294753339539732325056871 : (((p2 ∧ (p3 → True)) → (((p1 → (False ∧ (p4 ∧ (p4 ∧ p1)))) ∧ p2) ∨ (((True → (((True → p2) → p2) → p5)) ∧ True) ∨ True))) ∨ False) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196944143328876667108856024021 : (((((p1 ∧ (p1 ∧ True)) ∨ p1) ∨ p1) ∨ p5) ∨ ((p5 ∨ (p4 → (p4 ∧ p5))) → (False → ((p4 ∧ (p3 ∧ (True ∧ p1))) → (p5 ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h7.left
  let h9 := h7.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141348756995191746311452701624 : (((True ∧ (p1 ∨ (p1 ∨ p1))) ∨ ((((p2 ∧ p4) → (p1 → p1)) ∨ p4) ∧ (False → (((p2 → False) → p4) ∧ p2)))) → ((p2 ∨ True) ∨ False)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h9.left
    let h11 := h9.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_625078568580331070698596193223 : ((((True → ((((((p3 → p3) ∨ p3) ∨ p2) → (((p1 ∨ ((p2 → p2) → p3)) ∨ p4) ∧ p4)) → (p4 ∨ (p1 ∧ False))) → p2)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_127283849735000737760418919283 : ((p2 ∨ ((p1 → ((False ∧ True) ∧ (p2 → (p5 → ((p2 → (p1 ∧ (p5 → False))) ∨ ((False ∨ (p1 → p3)) ∨ p2)))))) → p1)) → (p3 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164867356618401312580133726783 : (((p4 ∨ (((p3 → p3) ∧ (p2 ∧ ((p5 ∨ p1) ∧ (False ∧ p1)))) ∧ (p3 → p4))) ∨ p5) ∨ (False → (((p1 → p2) ∨ True) → (p5 ∨ p2)))) := by
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
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207957665492744972441369996188 : (((p5 → (True ∧ p2)) ∧ (p4 → p3)) → (p1 → ((((False → p4) → (True → True)) → True) ∧ ((p2 ∧ (False ∨ p2)) ∨ (p4 → (True ∨ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h6
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245732572715498222521298914720 : ((p3 ∧ p2) ∨ (((True ∨ True) → ((True → p4) → (p3 ∨ p2))) → ((p3 ∨ (((p3 ∨ (p3 → (p2 ∨ p1))) ∧ True) ∧ (True ∧ True))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_655759371012693529367560146638 : ((((((True ∨ ((((p2 ∧ p3) ∨ p2) ∨ (p4 → False)) → ((True ∧ p1) → p2))) → (p4 ∧ p4)) ∨ ((False ∧ p3) ∨ True)) ∨ (p1 → p4)) ∨ False) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802403565391196103484815404669 : (((p2 → (False ∨ ((p4 → p4) → (False ∨ (((True ∧ (p1 ∧ (False → p3))) ∧ True) ∧ ((False ∨ (p2 → p5)) ∧ (p4 → (p4 ∧ p1)))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323277747261802017633272078893 : (p5 ∨ ((p2 → (False ∨ ((((p5 ∧ (p3 ∧ False)) ∧ (p3 ∨ p4)) ∨ (p5 ∨ (p1 ∧ p5))) ∧ (p1 ∧ (p5 → (True → p5)))))) ∨ (p4 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39462083591263458300799395415 : (((p5 ∧ (p3 ∧ (p1 ∧ ((p4 → (p3 ∧ p3)) ∨ (((True ∧ ((p5 → p2) ∨ p5)) ∨ ((p4 → p1) ∨ p5)) ∨ (p4 → p5)))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301879581353044830922871755076 : (False ∨ ((p4 → p5) ∨ (((False ∨ False) ∧ (((False ∨ (p2 ∨ p4)) ∧ p2) → (p4 ∨ (False ∧ p5)))) ∨ (((False → p4) ∨ (p5 ∧ p3)) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167689820875699748285598575074 : ((((((p2 ∨ p5) ∨ ((True ∧ p4) → p4)) ∧ p4) ∧ (p2 → False)) ∧ (p2 ∧ (p4 ∨ True))) → ((((p3 ∨ p1) ∨ (True → p5)) ∨ p2) → p3)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Conjunctions on the left can always be decomposed.
        let h6 := h1.left
        let h7 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h8 := h6.left
        let h9 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h12 =>
          -- Disjunctions on the left can always be decomposed.
          cases h12
          case inl h13 =>
            -- Conjunctions on the left can always be decomposed.
            let h14 := h7.left
            let h15 := h7.right
            -- Disjunctions on the left can always be decomposed.
            cases h15
            case inl h16 =>
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h17 =>
              -- One of the premise coincides with the conclusion.
              exact h5
          case inr h18 =>
            -- Conjunctions on the left can always be decomposed.
            let h19 := h7.left
            let h20 := h7.right
            -- Disjunctions on the left can always be decomposed.
            cases h20
            case inl h21 =>
              -- One of the premise coincides with the conclusion.
              exact h5
            case inr h22 =>
              -- One of the premise coincides with the conclusion.
              exact h5
        case inr h23 =>
          -- Conjunctions on the left can always be decomposed.
          let h24 := h7.left
          let h25 := h7.right
          -- Disjunctions on the left can always be decomposed.
          cases h25
          case inl h26 =>
            -- One of the premise coincides with the conclusion.
            exact h5
          case inr h27 =>
            -- One of the premise coincides with the conclusion.
            exact h5
      case inr h28 =>
        -- Conjunctions on the left can always be decomposed.
        let h29 := h1.left
        let h30 := h1.right
        -- Conjunctions on the left can always be decomposed.
        let h31 := h29.left
        let h32 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h33 := h31.left
        let h34 := h31.right
        -- Disjunctions on the left can always be decomposed.
        cases h33
        case inl h35 =>
          -- Disjunctions on the left can always be decomposed.
          cases h35
          case inl h36 =>
            -- Conjunctions on the left can always be decomposed.
            let h37 := h30.left
            let h38 := h30.right
            -- Disjunctions on the left can always be decomposed.
            cases h38
            case inl h39 =>
              -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
              have h40 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h37
              -- We have shown the premise of h32, we can now drive its conclusion.
              let h41 := h32 h40
              -- False on the left can always be used.
              apply False.elim h41
            case inr h42 =>
              -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
              have h43 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h37
              -- We have shown the premise of h32, we can now drive its conclusion.
              let h44 := h32 h43
              -- False on the left can always be used.
              apply False.elim h44
          case inr h45 =>
            -- Conjunctions on the left can always be decomposed.
            let h46 := h30.left
            let h47 := h30.right
            -- Disjunctions on the left can always be decomposed.
            cases h47
            case inl h48 =>
              -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
              have h49 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h46
              -- We have shown the premise of h32, we can now drive its conclusion.
              let h50 := h32 h49
              -- False on the left can always be used.
              apply False.elim h50
            case inr h51 =>
              -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
              have h52 : p2 := by
                -- One of the premise coincides with the conclusion.
                exact h46
              -- We have shown the premise of h32, we can now drive its conclusion.
              let h53 := h32 h52
              -- False on the left can always be used.
              apply False.elim h53
        case inr h54 =>
          -- Conjunctions on the left can always be decomposed.
          let h55 := h30.left
          let h56 := h30.right
          -- Disjunctions on the left can always be decomposed.
          cases h56
          case inl h57 =>
            -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
            have h58 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h32, we can now drive its conclusion.
            let h59 := h32 h58
            -- False on the left can always be used.
            apply False.elim h59
          case inr h60 =>
            -- We want to use the implication h32 based on <expert-advice>. So we show its premise.
            have h61 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h55
            -- We have shown the premise of h32, we can now drive its conclusion.
            let h62 := h32 h61
            -- False on the left can always be used.
            apply False.elim h62
    case inr h63 =>
      -- Conjunctions on the left can always be decomposed.
      let h64 := h1.left
      let h65 := h1.right
      -- Conjunctions on the left can always be decomposed.
      let h66 := h64.left
      let h67 := h64.right
      -- Conjunctions on the left can always be decomposed.
      let h68 := h66.left
      let h69 := h66.right
      -- Disjunctions on the left can always be decomposed.
      cases h68
      case inl h70 =>
        -- Disjunctions on the left can always be decomposed.
        cases h70
        case inl h71 =>
          -- Conjunctions on the left can always be decomposed.
          let h72 := h65.left
          let h73 := h65.right
          -- Disjunctions on the left can always be decomposed.
          cases h73
          case inl h74 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h75 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h72
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h76 := h67 h75
            -- False on the left can always be used.
            apply False.elim h76
          case inr h77 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h78 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h72
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h79 := h67 h78
            -- False on the left can always be used.
            apply False.elim h79
        case inr h80 =>
          -- Conjunctions on the left can always be decomposed.
          let h81 := h65.left
          let h82 := h65.right
          -- Disjunctions on the left can always be decomposed.
          cases h82
          case inl h83 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h84 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h81
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h85 := h67 h84
            -- False on the left can always be used.
            apply False.elim h85
          case inr h86 =>
            -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
            have h87 : p2 := by
              -- One of the premise coincides with the conclusion.
              exact h81
            -- We have shown the premise of h67, we can now drive its conclusion.
            let h88 := h67 h87
            -- False on the left can always be used.
            apply False.elim h88
      case inr h89 =>
        -- Conjunctions on the left can always be decomposed.
        let h90 := h65.left
        let h91 := h65.right
        -- Disjunctions on the left can always be decomposed.
        cases h91
        case inl h92 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h93 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h90
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h94 := h67 h93
          -- False on the left can always be used.
          apply False.elim h94
        case inr h95 =>
          -- We want to use the implication h67 based on <expert-advice>. So we show its premise.
          have h96 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h90
          -- We have shown the premise of h67, we can now drive its conclusion.
          let h97 := h67 h96
          -- False on the left can always be used.
          apply False.elim h97
  case inr h98 =>
    -- Conjunctions on the left can always be decomposed.
    let h99 := h1.left
    let h100 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h101 := h99.left
    let h102 := h99.right
    -- Conjunctions on the left can always be decomposed.
    let h103 := h101.left
    let h104 := h101.right
    -- Disjunctions on the left can always be decomposed.
    cases h103
    case inl h105 =>
      -- Disjunctions on the left can always be decomposed.
      cases h105
      case inl h106 =>
        -- Conjunctions on the left can always be decomposed.
        let h107 := h100.left
        let h108 := h100.right
        -- Disjunctions on the left can always be decomposed.
        cases h108
        case inl h109 =>
          -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
          have h110 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h107
          -- We have shown the premise of h102, we can now drive its conclusion.
          let h111 := h102 h110
          -- False on the left can always be used.
          apply False.elim h111
        case inr h112 =>
          -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
          have h113 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h107
          -- We have shown the premise of h102, we can now drive its conclusion.
          let h114 := h102 h113
          -- False on the left can always be used.
          apply False.elim h114
      case inr h115 =>
        -- Conjunctions on the left can always be decomposed.
        let h116 := h100.left
        let h117 := h100.right
        -- Disjunctions on the left can always be decomposed.
        cases h117
        case inl h118 =>
          -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
          have h119 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h116
          -- We have shown the premise of h102, we can now drive its conclusion.
          let h120 := h102 h119
          -- False on the left can always be used.
          apply False.elim h120
        case inr h121 =>
          -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
          have h122 : p2 := by
            -- One of the premise coincides with the conclusion.
            exact h116
          -- We have shown the premise of h102, we can now drive its conclusion.
          let h123 := h102 h122
          -- False on the left can always be used.
          apply False.elim h123
    case inr h124 =>
      -- Conjunctions on the left can always be decomposed.
      let h125 := h100.left
      let h126 := h100.right
      -- Disjunctions on the left can always be decomposed.
      cases h126
      case inl h127 =>
        -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
        have h128 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h125
        -- We have shown the premise of h102, we can now drive its conclusion.
        let h129 := h102 h128
        -- False on the left can always be used.
        apply False.elim h129
      case inr h130 =>
        -- We want to use the implication h102 based on <expert-advice>. So we show its premise.
        have h131 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h125
        -- We have shown the premise of h102, we can now drive its conclusion.
        let h132 := h102 h131
        -- False on the left can always be used.
        apply False.elim h132



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114528278578781369214690672027 : (((p1 ∨ (p2 ∧ (((p1 → ((p2 ∨ p2) → p4)) ∨ (p5 → p4)) ∨ ((p2 ∨ p5) ∨ p3)))) → ((True ∧ p4) ∨ (p4 ∧ False))) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316974365618899721934655482387 : (p3 ∨ (p3 → (((p5 ∧ (((False ∨ True) ∨ p1) ∨ ((p1 → p5) ∨ (p2 ∨ p4)))) → (False ∨ (((False → False) ∨ p1) → (False → p5)))) ∨ p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
        -- Implications on the right can always be decomposed.
        intro h10
        -- False on the left can always be used.
        apply False.elim h10
    case inr h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- Implications on the right can always be decomposed.
      intro h13
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h16
      -- Implications on the right can always be decomposed.
      intro h17
      -- False on the left can always be used.
      apply False.elim h17
    case inr h18 =>
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h20
        -- Implications on the right can always be decomposed.
        intro h21
        -- False on the left can always be used.
        apply False.elim h21
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h23
        -- Implications on the right can always be decomposed.
        intro h24
        -- False on the left can always be used.
        apply False.elim h24



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57516978678595463861627609186 : (((p4 → (p2 ∧ False)) ∨ (p4 → (True ∧ ((p5 ∨ (p3 → ((False ∧ (p4 ∨ ((p4 → p3) ∧ (False ∨ (True ∨ p4))))) ∧ p2))) ∨ False)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42335303107895571253833844533 : (((p3 ∧ ((True → ((((p1 ∨ (((p1 ∧ p2) → (True ∧ False)) ∧ False)) → p3) → p1) → (p4 → (False ∧ (p2 ∧ p3))))) ∨ p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340897458648327225332953688607 : (p2 → (((p5 ∧ ((p1 ∨ (p3 ∧ p4)) → ((p1 ∨ p1) ∨ (p5 ∧ p5)))) ∨ ((((p2 ∧ p2) → True) ∨ (p1 → p4)) ∨ (p5 → p3))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_780861207222633696683121888472 : (((p2 ∨ ((p1 ∨ (p5 ∨ (False ∨ p5))) → (((((p5 ∧ p1) ∨ (True ∧ False)) ∧ ((False ∨ True) → ((p4 ∨ p5) ∨ p1))) → p2) ∨ True))) ∨ False) ∧ True) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- False on the left can always be used.
        apply False.elim h6
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_801746321285277616149211428202 : (((p2 → (((p5 ∨ False) ∧ p5) ∨ (((((p4 ∨ p4) ∨ (((p5 ∨ p3) ∧ p5) → p5)) ∧ (p2 ∨ (False ∧ p5))) ∧ p5) ∨ (p4 → p2)))) ∨ p1) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38722275246262355952610200193 : (((((p4 ∧ (False → (False → True))) → False) → (((True → ((p2 ∨ p2) → p4)) ∧ ((True ∧ (False → (p5 → p4))) ∧ p2)) ∨ p2)) ∧ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260085916916325633919757358815 : ((p2 → False) → (p4 ∨ ((p2 → (p5 → False)) ∧ (((True ∧ ((p1 ∨ p4) ∧ ((p4 ∨ ((p1 ∧ p2) → (p1 ∧ False))) → p2))) ∨ True) ∨ False)))) := by
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
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118440807980672486784435047181 : ((p2 ∨ (p5 → ((p2 ∨ ((((p5 ∨ (p3 ∧ (p1 ∧ p3))) ∧ p3) → False) ∨ ((False ∧ (p5 → p2)) → (p2 ∨ p5)))) ∧ p2))) ∨ (p2 → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_706319887376640757531571118222 : ((((p4 ∧ (False → (True → (False ∧ (p3 → p3))))) ∧ (False ∧ ((((False → p5) ∧ (p5 → (False ∨ p4))) ∧ (False → p3)) ∧ (p1 ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_799814494077491316050788907018 : (((p1 → (p3 → ((p2 ∧ (p5 ∨ (p1 → (p3 ∨ True)))) ∧ ((((p4 ∨ p4) ∧ p2) ∨ (p1 → (p5 ∧ p2))) → ((p5 ∧ False) ∧ p2))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_620888594533192844439705141276 : (((((p2 ∨ p2) → (((False ∧ ((((True ∧ ((False ∨ p1) ∧ (p4 ∨ True))) → True) ∨ (p4 → True)) ∧ p4)) ∧ False) ∨ (p1 ∨ p3))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40046389890051241301594605847 : (((((p3 → (((p4 ∧ ((p5 → (p3 → (False → (((p1 → p1) ∧ (p4 ∧ p5)) ∧ True)))) → p5)) ∧ False) ∨ False)) ∧ p5) ∧ False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_262197867383382938775283621798 : (True ∧ (((((True → p5) → (p4 ∧ p3)) ∧ (((p1 ∧ p5) ∨ (p3 ∧ (True → (((p1 ∧ (True ∧ p2)) ∨ True) ∧ False)))) → p4)) → p2) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608749659162873739497918790796 : (((((((p4 ∧ ((False ∧ ((p4 ∧ p1) ∧ p4)) ∧ (p2 → p4))) ∨ (((p1 ∧ p5) → p2) ∧ True)) ∧ ((True ∨ p1) ∨ False)) ∨ True) ∨ p3) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53237173714808795538732793888 : (((((p3 ∧ p3) ∧ p3) ∨ (((p4 ∧ False) → p2) → (p2 ∨ p3))) ∨ ((False ∨ (p5 → ((True ∧ p4) ∨ p5))) ∧ ((p4 ∨ True) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57696757726146950441307976440 : ((((False ∧ p1) → p4) → (p1 ∨ (((((True ∧ p3) → (p2 → ((p3 → False) ∨ p4))) ∨ ((p2 ∧ (p3 ∧ p2)) ∨ p3)) ∧ p4) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_356528076347269410613788142051 : (p5 → ((((True ∨ p2) ∧ ((p2 ∧ True) ∧ p1)) ∧ (False ∨ p1)) ∨ (p2 → (p2 → ((((p1 ∨ p3) ∧ ((p1 ∧ p3) ∨ p4)) ∧ False) ∨ p2))))) := by
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
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138375685468535613912266528537 : ((p4 → ((((p5 → p3) ∨ True) ∨ p3) → (((False ∧ (((p2 ∧ True) ∧ p4) → p5)) ∧ (p3 → p4)) ∧ (p5 ∧ True)))) ∨ (p3 → (p2 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



