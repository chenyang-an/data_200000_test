variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134112124373890353807310313643 : (((((p2 → p5) ∨ (((False ∨ (((False ∨ p3) ∨ ((False → p3) ∧ p1)) ∨ False)) ∨ True) ∨ True)) ∧ (p3 ∨ True)) ∨ p1) ∨ (False ∧ (p4 ∧ p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776384690811707328869024302824 : (((p1 ∨ (((((p2 ∧ True) ∧ (p2 ∧ ((((False ∨ False) ∧ (p2 ∨ ((p4 → False) ∨ p2))) → True) → (p4 ∧ True)))) ∨ False) ∧ False) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114706171647461786867324398428 : (((((p4 → (p4 → p5)) → ((p5 ∧ (p3 → False)) → ((p1 → True) ∧ p4))) ∨ True) → (p3 ∨ ((p4 ∨ (p5 ∧ p4)) ∨ p1))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217061504535970896350417577163 : ((((p1 → True) ∧ p5) ∨ p1) → ((p1 → (False ∧ (p1 → p4))) → ((((p1 → ((p3 → p4) ∨ (p3 ∨ p3))) ∧ p4) ∧ (p5 ∨ p1)) ∨ True))) := by
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
theorem thm_5_vars_655903979879820024125422370371 : (((((((p2 ∧ ((p2 ∨ ((True → True) ∧ p5)) ∧ (p3 → p5))) → (p2 → p1)) ∧ p1) ∧ ((p5 ∨ (p2 ∨ p5)) → False)) ∨ (p4 ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_337791438778249125198225552579 : (p1 → (((p2 ∨ ((False → (p3 → ((p1 → p2) ∨ (p4 ∨ True)))) ∨ (p2 → p1))) ∨ p1) → ((True ∧ (p3 ∨ p3)) ∨ (p1 ∨ (p2 → p2))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h1
    case inr h5 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
      case inr h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h1
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_238757567952738762532725220285 : ((p1 ∨ True) ∧ ((p5 ∨ p5) ∨ (p5 ∨ (p2 ∨ (p4 ∨ (((p5 → (p4 ∨ p4)) ∨ (False → (False ∨ (p5 ∧ p3)))) ∨ ((p1 ∧ p3) ∨ p2))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259030830198066150760738402717 : ((True → p4) → (((p5 ∨ ((p3 → (True ∨ p1)) → (False ∨ False))) ∨ False) → ((p2 ∧ ((True ∨ (p2 → (p1 ∨ False))) → (p1 ∨ True))) ∨ p5))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
      have h6 : (p3 → (True ∨ p1)) := by
        -- Implications on the right can always be decomposed.
        intro h7
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h5, we can now drive its conclusion.
      let h8 := h5 h6
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- False on the left can always be used.
        apply False.elim h9
      case inr h10 =>
        -- False on the left can always be used.
        apply False.elim h10
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64288602118431959140182993004 : ((False ∨ (p2 → (True → ((p3 ∨ (((p5 ∨ (p2 ∨ p5)) ∧ p3) → (True ∧ p5))) → (((False ∧ (p4 → p1)) ∨ (p5 → True)) ∨ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_86092389277816465843251432506 : (((p2 → ((((p3 ∨ (p4 → p5)) ∨ p4) ∧ p1) ∧ p4)) ∧ (True → ((p2 ∨ ((p2 ∨ p4) ∨ ((True ∨ (p4 → True)) ∨ p2))) ∧ False))) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147270522153075285261848862687 : (((((p4 ∧ ((((p4 ∧ ((True ∨ p3) ∧ p5)) ∧ p5) ∨ (p1 → p4)) → p3)) → (p1 ∨ p3)) ∨ p4) ∨ p4) ∨ (((p4 ∨ p4) ∨ p3) → p4)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (((p4 ∧ ((True ∨ p3) ∧ p5)) ∧ p5) ∨ (p1 → p4)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53235320912065557356701262640 : ((((p4 ∧ (False ∧ p4)) ∧ (p1 ∨ (p5 ∨ ((p3 ∧ p3) ∧ p2)))) ∨ (p5 → ((((p2 → p1) ∧ p3) ∧ (p5 ∧ p3)) ∨ (p3 → p3)))) ∨ False) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704016917490175211966363617192 : (((((((p1 ∨ (False ∨ True)) ∧ p5) → (p2 ∧ p2)) → True) → (True → (p1 ∨ ((((p4 ∨ p3) ∨ (p2 ∨ p5)) ∧ True) ∨ (False ∧ p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_457743510700401278129967790803 : (((((((p1 → (p1 → ((p3 → (p4 → True)) ∧ p3))) → p1) ∧ p1) ∨ ((False ∧ p4) ∨ p5)) ∨ (False → ((p3 → False) ∨ (False ∨ p5)))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167304741290947582321076177032 : ((((((True ∧ ((False ∧ p1) ∨ False)) ∨ p2) ∨ (((True ∧ p1) → p2) → False)) → True) → False) → ((p4 → ((p5 ∨ False) ∨ False)) ∧ (False ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h3 : ((((True ∧ ((False ∧ p1) ∨ False)) ∨ p2) ∨ (((True ∧ p1) → p2) → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h3
  -- False on the left can always be used.
  apply False.elim h5
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : ((((True ∧ ((False ∧ p1) ∨ False)) ∨ p2) ∨ (((True ∧ p1) → p2) → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h6
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : ((((True ∧ ((False ∧ p1) ∨ False)) ∨ p2) ∨ (((True ∧ p1) → p2) → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h11 := h1 h9
  -- False on the left can always be used.
  apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189331476272463626175629415434 : ((True ∧ ((((p1 ∨ True) → (p1 ∧ p2)) ∧ p3) → True)) ∧ ((((p1 ∨ True) ∧ (((p5 → p3) ∧ (p3 → p3)) → p3)) ∨ (p5 ∨ True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258617932314302093298777687529 : ((p5 ∨ p4) → ((p1 → p1) → (p5 → ((((p5 ∧ (p5 ∨ False)) → (p5 → (p3 ∧ p1))) ∨ True) ∨ (((p4 → True) ∨ (p4 ∨ p2)) ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337218870644254242498396431620 : (p1 → ((((True ∧ p3) ∧ (False → p3)) ∧ ((False → (p1 ∧ (False ∨ (p5 ∨ p3)))) → ((p3 → ((p2 → p4) ∧ p2)) ∧ p5))) → (p4 ∨ p2))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h7 := h5.left
  let h8 := h5.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h9 : (False → (p1 ∧ (False ∨ (p5 ∨ p3)))) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h10
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h11 := h4 h9
  -- We need to get the left conjuct of h11 based on <expert-advice>.
  let h12 := h11.left
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350951338495453130319653260182 : (p4 → ((((((p2 ∨ p4) ∨ (p3 → False)) ∨ False) → (((True ∨ p3) ∧ (p4 → p1)) ∨ False)) ∧ (p3 ∨ (p1 → (True ∨ False)))) ∨ (False → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137887724581898748617426011463 : ((p4 ∨ ((((p1 → ((True → ((p1 → p2) ∧ (False ∧ p2))) → p4)) ∨ ((p2 → (p3 ∧ p5)) ∧ p1)) ∨ p4) → p1)) ∨ ((p3 ∨ p3) → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52472076444723989379578748328 : (((p3 ∨ (True → (((((p4 ∧ p5) ∧ p3) ∧ p1) → p4) → (False ∧ p3)))) ∧ (((p5 → True) ∧ ((False → False) ∧ (False ∨ p1))) → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_321062434951223171686958135223 : (p4 ∨ (p1 ∨ ((p2 → ((p1 ∨ True) → (p5 → (((True ∧ p3) ∨ False) ∧ (p3 ∧ (True → ((p2 → p5) ∨ (p4 ∧ p4)))))))) ∨ (p5 → p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113151009731734515851613625925 : (((p3 → (p2 ∧ ((((p5 ∧ True) ∨ (True → False)) → True) → ((((p5 ∨ (True ∧ p4)) ∨ (False ∨ p5)) ∨ p1) ∨ p1)))) → p3) ∨ (False → False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342969196392395385953246883409 : (p2 → (((p5 ∧ (p1 → p3)) ∧ p4) ∨ ((p4 ∧ (((True ∨ ((True ∧ p2) ∨ False)) → p2) → (p4 → p1))) ∨ (True → (p2 → (p2 ∧ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313306962913770160220843401325 : (p3 ∨ ((False ∨ (False ∨ ((p5 ∨ p5) ∨ (p1 → ((((p2 ∧ (p5 ∧ p4)) ∧ (((p4 → p4) ∧ p2) → (True ∨ p3))) ∧ p2) ∨ p4))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158779951961665114872641477497 : ((p5 ∧ ((((p4 ∧ p3) ∧ (p2 → False)) ∨ (True ∨ (p4 → (p2 ∨ (True ∨ (p1 ∧ True)))))) ∧ p5)) ∨ (p2 → (p3 → (p2 → (p1 → p1))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191776464051401509903744057781 : ((p1 ∨ ((p3 ∧ p1) ∧ (False ∧ ((p5 → p2) → p2)))) ∨ (False → (((False ∧ (p2 ∨ ((True ∧ p4) ∧ p3))) ∨ ((False ∨ p5) ∨ p2)) ∧ p4))) := by
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
theorem thm_5_vars_62318231882345386221792786842 : ((p3 ∧ ((p4 ∧ ((p2 → (((False ∨ p3) ∧ (p4 → p4)) ∧ ((p1 ∨ p2) → (p2 ∨ p5)))) ∧ ((p3 ∨ p4) ∧ p2))) ∨ (p3 → p3))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111683504086719691490790867350 : (((((False → (p3 ∨ ((p1 ∨ p5) ∧ ((True ∨ (p5 ∧ False)) ∨ (p4 ∧ (((p4 ∨ True) ∨ p1) ∧ p4)))))) ∧ True) → p1) ∨ p1) ∨ (p5 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214318592803130553705032578618 : (((False ∨ (p2 ∨ p2)) → p5) ∨ (p2 ∨ ((p2 → (((False ∨ ((p1 ∨ p1) ∨ ((p4 → True) ∧ (p2 ∧ p1)))) ∨ p2) ∧ (p5 → p3))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264429461452464244527839448248 : (True ∧ (((True ∧ (p2 → p4)) ∨ p2) → ((p5 → ((p1 → p3) → p1)) ∨ (((((p1 → (p3 ∨ p1)) ∨ p2) ∨ (p2 ∧ p4)) ∨ p1) ∨ p5)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_301838320916745597402928053187 : (False ∨ ((p4 ∨ p3) ∨ ((p1 → (p2 ∨ ((((((p5 → (p3 → (False ∨ p5))) ∨ p1) ∧ p4) ∧ (p2 ∧ p3)) ∨ (True ∧ True)) ∨ True))) ∧ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232906943674995112740495856388 : ((p3 ∧ (p3 ∧ p1)) → ((p1 → (p3 ∧ (False → p1))) ∧ ((p3 ∧ (((p5 ∨ p4) ∨ ((p5 ∧ (p1 ∧ True)) ∧ p2)) ∧ p4)) ∨ (True ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h7
  -- False on the left can always be used.
  apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_977657567875405865606030187175 : (((True ∧ (((p1 ∨ p5) → False) ∧ ((False ∨ p5) ∧ (((p1 ∨ (p3 ∨ p2)) ∨ p3) ∧ (((((p5 → True) → p2) ∨ p3) ∧ p5) ∨ True))))) → p2) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- Conjunctions on the left can always be decomposed.
    let h10 := h7.left
    let h11 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h12 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h14 =>
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Disjunctions on the left can always be decomposed.
          cases h15
          case inl h17 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h18 : (p1 ∨ p5) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h13
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h19 := h4 h18
            -- False on the left can always be used.
            apply False.elim h19
          case inr h20 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h21 : (p1 ∨ p5) := by
              -- Show the left disjunct based on <expert-advice>.
              apply Or.inl
              -- One of the premise coincides with the conclusion.
              exact h13
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h22 := h4 h21
            -- False on the left can always be used.
            apply False.elim h22
        case inr h23 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h24 : (p1 ∨ p5) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h25 := h4 h24
          -- False on the left can always be used.
          apply False.elim h25
      case inr h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h28 =>
            -- Conjunctions on the left can always be decomposed.
            let h29 := h28.left
            let h30 := h28.right
            -- Disjunctions on the left can always be decomposed.
            cases h29
            case inl h31 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h32 : (p1 ∨ p5) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h30
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h33 := h4 h32
              -- False on the left can always be used.
              apply False.elim h33
            case inr h34 =>
              -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
              have h35 : (p1 ∨ p5) := by
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- One of the premise coincides with the conclusion.
                exact h30
              -- We have shown the premise of h4, we can now drive its conclusion.
              let h36 := h4 h35
              -- False on the left can always be used.
              apply False.elim h36
          case inr h37 =>
            -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
            have h38 : (p1 ∨ p5) := by
              -- Show the right disjunct based on <expert-advice>.
              apply Or.inr
              -- One of the premise coincides with the conclusion.
              exact h9
            -- We have shown the premise of h4, we can now drive its conclusion.
            let h39 := h4 h38
            -- False on the left can always be used.
            apply False.elim h39
        case inr h40 =>
          -- Disjunctions on the left can always be decomposed.
          cases h11
          case inl h41 =>
            -- Conjunctions on the left can always be decomposed.
            let h42 := h41.left
            let h43 := h41.right
            -- Disjunctions on the left can always be decomposed.
            cases h42
            case inl h44 =>
              -- One of the premise coincides with the conclusion.
              exact h40
            case inr h45 =>
              -- One of the premise coincides with the conclusion.
              exact h40
          case inr h46 =>
            -- One of the premise coincides with the conclusion.
            exact h40
    case inr h47 =>
      -- Disjunctions on the left can always be decomposed.
      cases h11
      case inl h48 =>
        -- Conjunctions on the left can always be decomposed.
        let h49 := h48.left
        let h50 := h48.right
        -- Disjunctions on the left can always be decomposed.
        cases h49
        case inl h51 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h52 : (p1 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h50
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h53 := h4 h52
          -- False on the left can always be used.
          apply False.elim h53
        case inr h54 =>
          -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
          have h55 : (p1 ∨ p5) := by
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- One of the premise coincides with the conclusion.
            exact h50
          -- We have shown the premise of h4, we can now drive its conclusion.
          let h56 := h4 h55
          -- False on the left can always be used.
          apply False.elim h56
      case inr h57 =>
        -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
        have h58 : (p1 ∨ p5) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h9
        -- We have shown the premise of h4, we can now drive its conclusion.
        let h59 := h4 h58
        -- False on the left can always be used.
        apply False.elim h59
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113261645701705020655289941443 : ((((((False → True) → (False ∨ p1)) ∧ ((False ∨ (p1 ∧ ((p3 → p2) ∧ p1))) ∧ p1)) ∧ (p1 → (p3 → p4))) ∧ (p3 → p2)) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219095956853910125369796723909 : ((True ∨ ((p5 → p1) ∧ p2)) → ((((False ∨ p5) ∨ True) ∧ (((((p3 ∧ True) ∧ (p1 → False)) ∨ False) ∧ (p4 ∧ p2)) ∧ p2)) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_712097840970116196627048118010 : (((((False ∨ (p4 ∧ (p4 ∧ False))) ∨ False) ∨ (((True ∧ False) ∧ (p1 ∨ ((((True ∨ p4) → (True → (p2 ∧ p1))) ∧ p3) ∧ p1))) → p3)) ∨ False) ∧ True) := by
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
  let h4 := h2.left
  let h5 := h2.right
  -- False on the left can always be used.
  apply False.elim h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40821885969441888701038255145 : ((((p5 ∨ (True ∨ ((False → ((p3 → (False → ((p5 → p1) → ((p3 ∨ p4) → False)))) ∧ False)) ∨ ((p3 ∨ p1) ∨ True)))) → False) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693965795417669177814904538871 : (((((((p4 ∧ (True ∨ p2)) ∧ p1) ∨ (True ∧ (p5 ∨ p2))) ∨ (p3 ∧ True)) ∨ (True → (((p3 → (p4 → True)) ∨ False) → (False → p4)))) ∨ p5) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122791309061723918908674324511 : (((p4 → ((p4 → (((p3 ∧ p4) ∧ ((p3 ∨ p2) → (((False ∨ p2) ∨ p5) → True))) → (p3 → p2))) ∧ p1)) → (p5 ∧ p1)) → (p1 → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218207464394713416590224363929 : (((p3 ∧ p1) ∨ (p1 ∨ p5)) → (((p3 ∧ p4) ∧ p1) → ((False ∨ p2) ∨ ((True ∨ p3) ∧ (((p1 ∧ (p2 → p3)) ∨ p5) → (True ∨ p3)))))) := by
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
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h10
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Conjunctions on the left can always be decomposed.
      let h12 := h11.left
      let h13 := h11.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h14 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h17
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Conjunctions on the left can always be decomposed.
        let h19 := h18.left
        let h20 := h18.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h21 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h22 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h23
      -- Disjunctions on the left can always be decomposed.
      cases h23
      case inl h24 =>
        -- Conjunctions on the left can always be decomposed.
        let h25 := h24.left
        let h26 := h24.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h27 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_347211389629052071379471250329 : (p3 → ((p3 → ((((p3 → (p2 ∨ (p3 ∧ p3))) ∧ p1) ∧ True) ∨ p4)) ∨ (p5 ∨ ((((False ∨ False) → True) → p2) ∨ ((True ∨ p5) → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193532286307387133033383473988 : (((p5 → p4) ∨ (p3 → ((p3 ∨ (p2 → p5)) ∧ p5))) → (((p5 ∧ (p3 ∨ ((p3 ∨ (p4 → p5)) ∧ p3))) → (p4 ∧ p1)) → (p4 → p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_791348653628778617393087730748 : (((True → ((((False → False) ∧ (False ∨ (((((p3 ∨ p4) ∧ p3) ∧ (((p4 → p5) ∨ p3) ∨ p1)) ∧ p5) ∨ False))) ∨ (True → True)) ∨ True)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315414672622338428598198352255 : (p3 ∨ (((p3 ∨ p5) → p3) ∨ ((((p5 ∨ True) ∨ (False ∧ ((((p2 → p1) ∧ True) → True) → p4))) → (p4 ∧ False)) → (False ∧ (False → p5))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p5 ∨ True) ∨ (False ∧ ((((p2 → p1) ∧ True) → True) → p4))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
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
  -- Implications on the right can always be decomposed.
  intro h5
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_708719390391851372247370034427 : (((((((p4 ∧ p3) → True) ∨ (p4 ∧ p1)) → p3) → (p2 ∧ ((True ∧ p2) ∨ ((False ∧ (p5 ∧ (False ∨ (p3 ∨ p2)))) ∧ (p3 → p4))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167308391762202015119599165613 : (((((p3 → False) ∧ ((((p5 ∨ (p1 → p2)) ∧ True) → p1) → (True ∧ p3))) → False) → p4) → (((p5 ∧ (p3 → p4)) → (p4 ∨ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173913539022310453929115266553 : ((((True ∨ (p2 ∧ (True → ((p5 → p3) ∧ (True → (p4 ∨ p5)))))) → p5) → True) → (True ∧ ((((p5 ∧ p2) ∧ (p2 ∨ False)) ∨ p3) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_303795837869974057382942161204 : (p1 ∨ ((((p2 ∨ (True ∧ ((p5 ∧ (False ∧ (p1 → True))) ∨ (((p1 → ((p1 → p3) ∨ True)) ∧ p4) → True)))) ∨ (False ∧ p2)) → p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_664579859371887156105377535769 : ((((p5 ∨ (True ∨ ((True → ((p4 ∧ ((True ∨ False) ∨ p2)) → (p1 ∨ ((p3 ∨ p4) ∨ (p5 → (p1 ∨ p1)))))) ∧ p5))) → (p4 ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113440753014929500804914184779 : (((((True ∨ (((p4 → p4) ∧ p1) ∨ p5)) → (((True ∧ (p5 → p3)) ∧ (p1 → p5)) ∧ (p4 ∧ p1))) ∨ p1) ∨ (False ∨ p1)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165226340902723233513839082505 : (((((p4 → p1) → False) ∧ (((p4 ∧ (p3 ∧ (True ∨ p2))) → False) ∨ p4)) ∨ (True → p1)) ∨ (False → ((p4 ∨ p4) ∨ (p1 ∧ (p2 ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_33067319689285791991492003467 : ((p3 ∨ ((p3 ∨ (True ∧ True)) → ((p2 ∨ False) → ((((p1 ∧ p1) ∨ p1) → False) ∨ ((p5 ∧ (True → ((p3 → p4) → p2))) ∨ True))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h1
    case inl h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42877859107363028056501621334 : (((p2 → (p3 → ((p4 ∧ ((p1 → ((True → (p3 → ((False → p2) ∧ ((p5 ∨ False) ∧ p1)))) ∨ (p4 ∧ p5))) ∨ True)) ∨ p3))) ∨ p2) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_50215450632655002324196357833 : (((((((p4 ∧ p3) ∧ (False ∧ p3)) ∧ p5) ∧ (((p4 ∨ (p5 → p2)) → (True → p4)) → False)) ∨ p3) ∨ ((p3 ∧ (p1 → False)) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_256848498432476366268067260382 : ((p1 ∨ p3) → (((p2 ∧ (p1 ∧ False)) ∧ p2) ∨ ((p3 ∨ p1) ∧ (((p5 ∧ (p2 ∧ (p5 ∨ p1))) ∨ p3) → (True ∨ (False → (True → False))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h12
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- Disjunctions on the left can always be decomposed.
      cases h18
      case inl h19 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h20 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h21 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_68462188367122329294913449663 : ((p3 → (p3 ∧ (((p2 ∧ (((p4 ∨ (False ∧ p3)) → (p1 ∧ True)) ∨ ((False ∨ p1) ∨ p5))) ∧ (p1 ∨ ((p5 ∨ p5) ∧ True))) ∨ p3))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50888574758152705167575816758 : ((((((p3 → p5) ∨ p2) → (False → ((p1 ∨ ((p5 ∨ (False → p5)) ∧ p1)) → p1))) → p1) ∧ ((p1 ∨ ((p3 ∨ False) ∨ p5)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_755038450699044583760824113349 : (((False ∧ (True → (p5 → ((False → (p5 ∧ (((p3 ∧ p5) → (((p4 ∨ True) ∨ p5) ∨ p1)) ∨ p5))) → (p2 ∨ (p1 ∧ (p4 → p1))))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190047872665032891028950097346 : ((((False ∧ (p5 ∧ (p5 → (p3 ∨ p1)))) ∨ p3) ∧ p3) ∨ (((True ∨ p5) → ((p5 → (False ∧ True)) ∨ (True ∧ ((True ∧ p1) ∧ p1)))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53140644746499071127203751753 : ((((p5 ∧ (True ∧ (p2 ∨ ((p5 → (True ∨ p5)) → p4)))) ∧ p5) ∨ ((((((False ∨ (p5 → p5)) → False) → True) ∨ p2) ∧ p1) ∧ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_649952968869032581485702249364 : (((((((((True ∧ p5) ∨ ((p5 ∨ True) ∨ (False → p2))) → p5) → (False ∨ (p3 → p4))) ∨ True) ∨ ((True → False) ∧ False)) ∧ (False → p2)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40372259406431728638832950642 : (((((True → (p1 → ((((p1 → (p4 ∧ p1)) → (p2 ∨ (p4 → p4))) ∨ (p3 ∧ ((p5 ∨ True) ∨ False))) → p4))) → False) ∨ p4) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42248368993028037811983953977 : (((False ∧ (p3 → (False ∧ ((((p5 ∧ p1) ∧ p1) → True) ∧ (((p4 → ((p4 ∨ (p4 ∧ p5)) → (p4 → p2))) → p5) ∧ p1))))) ∨ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205025027536182300833162698390 : (((p3 ∨ (p2 ∨ (p2 ∧ p5))) → False) ∨ (p1 → ((((p3 ∧ (p2 → p2)) ∧ p1) → (p5 ∨ (((False → False) ∨ (True ∨ True)) → p4))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172013813527154717952931889760 : (((((p5 ∨ (p4 → (p5 ∧ p1))) ∧ True) → ((True ∧ p5) ∨ p5)) ∨ (p1 ∨ p3)) ∨ (True ∨ (((True → (False → p1)) → (False → p4)) ∧ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_747134913658055187525145022837 : ((((p5 ∨ True) → ((p2 ∧ (((p4 ∨ ((p4 ∨ p3) → p5)) ∨ (p3 ∧ (p5 → (p5 ∨ p1)))) → (False ∨ p2))) → ((True → p5) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337114169298490885117426204812 : (p1 → (((p2 ∨ p3) ∨ (p1 ∧ (((p5 → ((p3 ∧ ((p2 → True) ∨ (p1 ∧ True))) ∨ p5)) ∧ p5) ∨ (True → (p3 ∨ p3))))) ∨ (True → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45059078550625153839157836062 : ((((p3 → False) ∨ ((p3 ∧ ((p4 ∨ p5) ∨ ((False ∧ (False ∧ (False → (p1 ∨ (p1 ∧ p4))))) ∧ ((p2 ∨ p1) → False)))) → p5)) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246586220639193041015728944868 : ((p5 ∧ p2) ∨ ((p4 ∧ (p5 ∨ (p3 ∨ True))) → (((p4 ∧ ((p2 ∧ ((p4 → (p2 ∧ p5)) → p3)) → p3)) → p1) → ((p1 → p5) ∨ p4)))) := by
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
  cases h4
  case inl h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354862345875736335249785187315 : (p5 → (((p1 → p2) → ((p1 ∨ ((p5 ∨ p2) ∨ (True ∧ p1))) → (((p1 ∨ (p5 ∨ (False → (p1 ∧ p5)))) ∨ p2) → (p3 ∧ p3)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300369986426970957868696574874 : (False ∨ (((p1 → ((False → ((((p3 ∧ ((True ∧ True) → (p1 ∨ True))) ∨ (p2 → p3)) ∧ p1) → p4)) ∧ False)) → p2) ∨ (p3 → (False → p1)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338845590435849208692288088854 : (p1 → ((p1 → p3) ∨ ((((True ∧ p5) ∨ False) ∧ p2) → (p5 ∧ ((p4 → (p4 → True)) → (((p1 ∧ p1) ∧ (p3 → False)) ∨ (p3 ∨ p2))))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  -- Implications on the right can always be decomposed.
  intro h9
  -- Conjunctions on the left can always be decomposed.
  let h10 := h2.left
  let h11 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h10
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h15 =>
    -- False on the left can always be used.
    apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248261334973978563907876928729 : ((p2 ∨ p2) ∨ ((p2 → ((p2 ∨ (p4 ∧ ((p1 ∨ ((p1 ∨ ((p3 ∨ (p3 ∧ (p5 → p5))) ∨ p5)) → (p3 ∧ p2))) ∨ False))) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186532822819902849507479438337 : ((((p4 ∧ (((False ∨ p4) ∨ False) → False)) → True) ∨ (p2 → p4)) → ((((((p2 → p4) → True) ∧ True) → p5) ∨ True) ∨ ((True → True) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149013423585195339938283475620 : ((((p2 ∧ p2) ∨ p1) ∨ ((((p4 → False) ∨ ((p4 ∧ p5) ∧ False)) → ((p5 ∨ p1) ∧ (True → p2))) ∧ p3)) ∨ ((p1 ∨ p2) → (p2 → p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47615316190238693480497788455 : (((p4 → (p5 → ((False ∨ p1) → ((p1 → (p1 → ((((False → (p1 ∧ True)) ∧ p3) → p1) ∨ (p5 → p5)))) → False)))) ∨ (p3 ∨ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342221157336005331435708467811 : (p2 → ((p3 ∧ ((p1 ∨ p4) ∧ (((p1 ∨ (p5 ∧ (p3 ∧ p4))) ∨ (False ∨ (p1 ∨ (True ∨ True)))) ∧ p1))) → ((True ∧ (False ∧ p3)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Conjunctions on the left can always be decomposed.
  let h5 := h4.left
  let h6 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h6.left
    let h9 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h12 =>
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- False on the left can always be used.
        apply False.elim h18
      case inr h19 =>
        -- Disjunctions on the left can always be decomposed.
        cases h19
        case inl h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h21 =>
          -- Disjunctions on the left can always be decomposed.
          cases h21
          case inl h22 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h23 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
  case inr h24 =>
    -- Conjunctions on the left can always be decomposed.
    let h25 := h6.left
    let h26 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h25
    case inl h27 =>
      -- Disjunctions on the left can always be decomposed.
      cases h27
      case inl h28 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h29.left
        let h31 := h29.right
        -- Conjunctions on the left can always be decomposed.
        let h32 := h31.left
        let h33 := h31.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h34 =>
      -- Disjunctions on the left can always be decomposed.
      cases h34
      case inl h35 =>
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- Disjunctions on the left can always be decomposed.
        cases h36
        case inl h37 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h38 =>
          -- Disjunctions on the left can always be decomposed.
          cases h38
          case inl h39 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h40 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234617434313742852395291475886 : ((p3 → (True → p2)) → (p5 ∨ ((p3 ∧ ((True ∧ (p5 ∨ p1)) → ((((False ∨ p2) ∨ (False ∧ p2)) ∨ ((p5 ∨ p1) → p5)) → p2))) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65185390592371538954145543786 : ((p3 ∨ ((False ∧ ((p2 ∧ p4) ∨ ((((((p5 ∧ p1) ∨ (p4 ∨ True)) ∧ False) ∧ False) ∧ (p3 ∨ ((False → False) ∨ True))) ∧ True))) ∧ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_633640060673817422363505672515 : ((((((True → p1) ∨ (p4 ∨ ((True ∨ False) → (False ∧ ((True ∨ (True ∨ ((True ∨ (False ∨ p5)) → p5))) ∨ p3))))) ∨ (p4 → p4)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50010080350925585756885253619 : ((((p5 → (p2 ∧ ((p3 ∧ p1) ∧ (p3 ∨ p2)))) → ((True ∧ (p4 → (p5 ∧ (p1 ∨ p3)))) → p3)) ∧ (((True ∨ p4) ∨ p5) ∨ p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340213888723179932241939580863 : (p1 → (p5 → ((p5 → (((p3 ∨ (((p3 ∧ (((True ∨ (True ∨ (p4 ∨ p2))) ∨ p5) ∧ p5)) ∨ True) ∧ (False ∨ p1))) ∨ p1) → p4)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116360013391798087567346988886 : ((((p4 → p1) ∨ False) → ((p3 ∧ ((False → False) ∧ p2)) ∨ (((((p5 → p5) ∧ p3) ∧ p2) ∨ p4) ∨ (True → (p4 → p4))))) ∨ (p5 → False)) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_55652856047638180202795351078 : ((((True ∧ (p5 ∨ p4)) ∧ p2) ∧ (((((False ∧ False) ∨ p1) ∨ p2) ∨ True) → ((p4 → (p2 ∨ (p5 ∨ (p4 ∧ (p2 ∧ False))))) → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_18314884767838082515932001245 : (((((p4 ∨ p1) ∧ (False → False)) ∧ (((((p4 → (False ∧ p4)) → p5) → True) ∨ p1) ∨ (p1 ∧ p5))) → ((p3 ∨ p4) ∨ (True → True))) ∧ True) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h9 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
    case inr h10 =>
      -- Conjunctions on the left can always be decomposed.
      let h11 := h10.left
      let h12 := h10.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Conjunctions on the left can always be decomposed.
      let h20 := h19.left
      let h21 := h19.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h22
      -- True on the right can always be proven directly.
      apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58201941457492894802365468032 : (((p4 ∧ True) ∧ (p3 ∨ (p3 ∨ ((True → p1) → ((p4 ∨ False) ∨ (True → (True ∨ ((p4 → (p3 → False)) ∧ (True ∨ (p4 ∨ p1)))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225824867737499237116307165940 : (((True ∧ p3) ∨ p5) ∨ ((((((p2 ∧ (True → (p3 → True))) → (p1 ∨ (p2 ∨ p4))) → p3) ∧ (p5 ∧ p3)) ∧ p1) ∨ (p2 ∨ (True ∨ p3)))) := by
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
theorem thm_5_vars_311293771446247245987006386217 : (p2 ∨ (True ∧ (True ∧ (((((p2 ∧ p3) ∧ p4) ∧ ((p3 ∧ False) ∨ ((p1 ∨ (p5 ∧ True)) ∨ (((p5 ∧ p3) → False) → p2)))) ∨ True) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
theorem thm_5_vars_322866492829894728808195045264 : (p5 ∨ (((p4 ∧ ((False ∨ False) ∨ p2)) ∧ (p4 → ((p3 → (p2 ∨ ((((p4 ∨ p2) ∨ p1) ∧ True) → (p3 → p4)))) ∧ (False ∨ False)))) → p5)) := by
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
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- We need to get the right conjuct of h11 based on <expert-advice>.
    let h12 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- False on the left can always be used.
      apply False.elim h13
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213428166187854064621586763848 : (((p3 ∨ (True → p5)) ∧ p3) ∨ (((p2 ∧ (p4 ∨ p3)) ∨ True) ∨ (((False ∧ p2) ∧ (p1 ∧ p4)) → ((False → p2) ∨ ((p5 → p1) ∧ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47807503919493075440144608167 : (((((((p4 ∨ (p5 → (True ∨ p1))) → (True → (p5 → (p3 ∧ False)))) → ((p3 ∧ p2) → p2)) → (p1 ∧ True)) → p1) → (p1 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_734517986004876797950893302930 : ((((p1 ∨ False) ∧ (p2 ∨ (p2 ∧ (False ∨ (((((False ∧ ((False ∨ p1) ∨ True)) → (p2 → p2)) → p3) → (p1 ∨ (p3 ∧ p3))) ∨ p1))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177967397048658650942981799912 : ((((p1 ∨ False) → (p3 ∨ ((p4 → (p5 ∨ (False ∧ p2))) ∨ p4))) ∨ p4) ∨ ((p2 ∨ (True → p1)) → ((p4 → True) ∨ (False ∨ (True ∨ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201084228560860500562627109902 : ((p5 ∨ (True ∨ (True ∧ ((False ∨ p1) → True)))) → (p3 ∨ (((p4 ∨ p2) ∨ (p2 → (False ∨ (False → (p1 ∨ p2))))) → (p5 ∨ (False → p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h6 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h2
    case inr h7 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h10
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Disjunctions on the left can always be decomposed.
        cases h11
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h13
          -- False on the left can always be used.
          apply False.elim h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h17
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h21
      -- Disjunctions on the left can always be decomposed.
      cases h21
      case inl h22 =>
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- False on the left can always be used.
          apply False.elim h24
        case inr h25 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h26
          -- False on the left can always be used.
          apply False.elim h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- False on the left can always be used.
        apply False.elim h28



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251402798570942697885484271294 : ((p2 → p4) ∨ (True → (((p5 ∨ ((True ∧ ((p2 ∧ p1) → p4)) → ((p1 ∧ p4) ∧ True))) ∨ (p2 ∨ (p4 → (p3 ∧ (p1 ∨ p3))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803308684782006752764547726321 : (((p3 → ((((p5 ∨ (p3 → (True ∧ (p4 ∨ p2)))) → p3) → ((p1 ∧ p3) ∨ ((p5 ∨ (p3 ∨ p3)) → (p3 ∧ (p3 ∧ p1))))) ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668020059726413590607598944659 : ((((p4 ∨ (p3 ∨ (((p5 → ((p5 ∧ p3) → ((p4 ∨ p4) → p2))) ∨ (p4 ∧ False)) ∧ (p2 → (True ∨ p5))))) ∧ (p3 ∧ (p5 ∧ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167617838442428278162874933819 : (((((p3 ∨ ((((p3 → False) ∧ p1) ∧ (p1 ∧ p1)) ∧ False)) ∧ p4) ∨ True) → (p3 ∧ p4)) → (((p4 ∨ (p5 → p4)) → p1) ∨ (p4 ∧ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p3 ∨ ((((p3 → False) ∧ p1) ∧ (p1 ∧ p1)) ∧ False)) ∧ p4) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h4
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300195195672516825718752298742 : (False ∨ (((((p2 ∨ ((False ∧ False) ∧ False)) → (False ∧ True)) ∨ ((p2 ∧ False) ∨ (True ∨ ((p4 ∨ False) ∧ (p5 ∨ p4))))) → False) → (p4 ∨ p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p2 ∨ ((False ∧ False) ∧ False)) → (False ∧ True)) ∨ ((p2 ∧ False) ∨ (True ∨ ((p4 ∨ False) ∧ (p5 ∨ p4))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



