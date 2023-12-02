variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670420155870616389428642237506 : (((((p5 ∧ (p3 ∨ p4)) → (((False ∨ p1) ∨ (((p5 ∧ ((p3 ∧ (p5 ∨ p1)) ∨ p2)) ∨ p2) ∨ False)) ∧ True)) ∨ ((p1 ∨ p2) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_63033394655513527591016544566 : ((p5 ∧ (((p1 ∧ (((p3 → (False ∨ p5)) ∧ (p3 ∧ (p4 → True))) ∨ (p5 ∧ (p4 → ((p4 ∧ (p1 ∧ p3)) ∧ p3))))) ∧ p3) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172783751139315668863210244453 : (((True → True) → ((p1 ∨ p4) ∨ (((p5 ∧ p3) ∨ p1) ∨ ((p4 ∨ p4) ∨ p5)))) ∨ (((((p4 ∧ p5) ∨ p3) ∧ p3) ∧ False) → (p1 → p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185165348660268403007182978898 : (((True → p3) → ((True → p4) ∧ (p2 ∨ ((p2 ∧ p5) → p4)))) ∨ ((p5 → ((p5 → False) → (p5 → p2))) ∨ (False ∧ ((p2 ∨ p4) ∧ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_258573734977418738695836126128 : ((p5 ∨ p3) → (p5 → (((True ∨ p5) ∧ (p2 ∨ ((((p3 → (False ∧ True)) ∨ True) ∧ (p1 ∧ (((p5 ∨ False) ∨ p1) ∧ True))) ∧ p2))) ∨ p5))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114188269516808637458902198375 : (((((((p4 ∧ ((p4 → p1) ∧ p4)) ∨ p3) ∨ p2) ∧ (p5 → p3)) ∨ ((p3 ∧ p4) ∨ (p1 → p5))) → (p2 ∨ (p5 ∨ True))) ∨ (p5 → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Conjunctions on the left can always be decomposed.
        let h7 := h6.left
        let h8 := h6.right
        -- Conjunctions on the left can always be decomposed.
        let h9 := h8.left
        let h10 := h8.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h12 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h17 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58906458726041654819030105768 : (((p1 ∧ True) ∨ ((p4 ∧ (p1 → ((((((p1 ∧ p5) ∨ p2) ∨ False) ∧ p3) ∨ ((p4 ∨ (p3 ∨ (p1 → p1))) ∧ p4)) → False))) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227760488685148083130950402395 : ((p1 ∧ (p5 ∨ True)) ∨ (p2 → (((p3 → (p1 → p4)) → (p1 → (p3 → (p5 ∧ p3)))) ∨ (p3 ∨ (True ∨ ((False ∧ False) ∨ (p2 ∧ False))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_136544486862797283319057456914 : ((((p1 ∨ p1) ∧ p4) ∨ ((False ∨ p3) ∨ (True ∧ ((p3 ∨ ((((p3 ∨ p2) ∧ p5) → p5) → p3)) ∧ (p1 ∨ p2))))) ∨ ((True ∧ p3) → p3)) := by
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
theorem thm_5_vars_185717621785057757609737788489 : ((p2 → (p2 ∧ (((p2 → (p1 → p3)) ∨ False) → (p3 ∧ p1)))) ∨ ((((False ∨ p5) ∨ p2) → (((p4 → (p5 ∨ p4)) ∧ p4) ∨ True)) ∧ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22868751992472119448229021843 : (((((p3 ∧ p4) → p1) → (p1 → False)) ∨ (p5 ∨ (((p3 ∨ p3) ∧ p3) → (p1 ∨ ((p2 ∨ (p3 ∨ False)) ∧ ((p3 ∧ True) ∨ p1)))))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69742626212929282236522774763 : (((((((p1 → p2) ∧ (p5 ∧ ((p2 ∧ (p5 ∧ ((p4 ∨ p2) → (False ∧ (p1 ∧ p4))))) ∧ False))) ∨ (True ∨ False)) → p5) ∨ False) ∧ p2) → p5) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h5 : (((p1 → p2) ∧ (p5 ∧ ((p2 ∧ (p5 ∧ ((p4 ∨ p2) → (False ∧ (p1 ∧ p4))))) ∧ False))) ∨ (True ∨ False)) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h6 := h4 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137166573447797923058456919919 : ((False ∧ (((p3 ∨ (False → (True ∧ (False ∨ (p5 → p3))))) → ((p5 ∧ ((p4 ∧ True) ∧ p5)) ∨ False)) ∧ (p1 → p4))) ∨ (p2 ∨ (p3 → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64053283817981836270871390678 : ((False ∨ (((True ∧ (p4 → False)) ∧ ((((p5 → p3) → (p4 → (False → (p1 ∧ True)))) ∨ p4) → p3)) ∧ ((False ∧ (True → p5)) ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_673043366973265154631318624224 : ((((((p2 ∨ True) → (p5 ∨ ((True ∧ ((p5 ∨ (p5 → True)) ∧ p3)) ∨ p2))) → ((p5 → p1) ∧ (p5 ∧ p4))) → (p4 ∧ (False ∨ p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_214808642549946434776112489007 : (((p2 ∨ p5) ∨ (p1 → False)) ∨ ((((((True ∨ p5) ∧ False) ∨ p5) ∧ (p2 ∨ (True → (p3 → (p4 ∧ p5))))) ∨ (p1 → (p1 ∨ True))) ∨ p4)) := by
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
theorem thm_5_vars_793487466722318990679458948680 : (((True → (p1 ∨ (((((p4 → (False ∧ p4)) ∨ ((False ∨ True) → ((p2 ∨ p1) ∧ (p2 ∧ (p1 ∨ (p4 → False)))))) → p2) ∧ p3) ∧ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117615904747184319726792112261 : ((p3 ∧ ((((((p5 ∨ p3) ∨ ((p3 → p4) ∨ p3)) ∧ (True ∧ (((p1 ∨ False) → p2) ∧ (False → p2)))) → p4) ∧ p3) ∧ p3)) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185187312781631892072444749499 : ((True ∧ (((p3 ∧ p1) ∧ (((p5 ∨ p3) ∨ p2) → p3)) ∧ False)) ∨ (False → ((p5 ∨ ((p4 → (False → False)) ∨ False)) → (p2 → (p2 → True))))) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138335055247014637478083732046 : ((p3 → (p3 → (((p2 ∧ ((p2 ∧ False) → (p1 ∧ (False ∧ True)))) → p2) → (((p2 ∨ True) ∧ (False ∨ p1)) ∨ False)))) ∨ (p4 → (False → False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_146912336714915272294982677069 : (((((p4 ∧ (False ∨ ((((p5 ∨ p3) → p3) ∧ (p5 ∧ p2)) ∨ (p1 ∨ False)))) → (True ∧ p1)) ∧ False) ∧ p5) ∨ (((p1 ∨ p2) → p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_167061736863647710580501997241 : ((((p3 ∧ ((p2 → (((p4 → (True ∨ p1)) ∨ False) ∧ (p5 → p3))) → p5)) ∨ p4) ∨ True) → (((p1 → p2) → p5) ∨ ((False → False) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Disjunctions on the left can always be decomposed.
    cases h2
    case inl h3 =>
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- False on the left can always be used.
      apply False.elim h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
  case inr h8 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157977445105652459085868839826 : (((p2 → (True → (False ∨ ((p5 → p4) ∧ p1)))) ∨ ((((p4 → p4) ∧ (p3 ∨ p4)) ∧ True) → False)) ∨ (((p1 → p2) → (p5 ∧ p2)) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57810572946665604057704756597 : (((p2 ∧ (p1 → p3)) → (p4 ∨ ((True ∨ (((p2 ∨ (p4 ∧ p2)) ∨ p1) → (((False ∧ (p3 → True)) ∨ (p1 → p1)) ∨ p2))) → False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306465078382824480488214984785 : (p1 ∨ ((p5 ∨ False) ∨ ((p2 ∨ p2) → ((p1 ∧ p3) ∨ (((p3 ∧ p1) ∨ (p3 ∨ (False ∧ ((False → p2) → (p3 ∨ p2))))) → (p5 ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
      -- Conjunctions on the left can always be decomposed.
      let h5 := h4.left
      let h6 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h2
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- False on the left can always be used.
        apply False.elim h10
  case inr h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h13
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h12
    case inr h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h17
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h19 =>
        -- Conjunctions on the left can always be decomposed.
        let h20 := h19.left
        let h21 := h19.right
        -- False on the left can always be used.
        apply False.elim h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113654126904907498263659106645 : ((((True ∧ (((p3 ∧ (False ∧ (p5 ∨ p4))) → (p5 ∨ ((((p1 ∨ True) ∧ p1) ∨ True) ∧ True))) ∧ p4)) ∧ True) → (False ∧ p3)) ∨ (True ∨ p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148373024558619771516510334199 : ((((((p5 ∧ p5) → (False ∨ (p2 ∨ (p3 ∧ (p1 → p1))))) ∨ p4) → False) ∨ (p1 ∨ ((p5 ∧ False) → False))) ∨ ((p2 → False) ∧ (p5 ∨ True))) := by
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
theorem thm_5_vars_67980084514235549650618992347 : ((p2 → ((p1 → (p5 ∧ p3)) → (((((p3 ∧ (p2 ∨ True)) ∨ True) → (((True → False) ∨ p1) ∨ ((p4 ∨ p5) → p2))) ∧ p5) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148897611824867180682135830418 : (((p4 ∧ (p2 → (False ∨ p2))) ∨ (((((p5 ∨ (p1 ∧ p5)) → (False → False)) ∨ (p3 → p2)) ∨ p3) → False)) ∨ ((False ∨ False) → (p3 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66304234857447655877752823453 : ((p5 ∨ ((p2 ∧ p2) → (((p3 → p4) ∧ False) ∧ ((False ∨ ((((p4 → p2) ∧ p1) ∨ ((p3 → True) → p1)) ∧ p2)) ∨ (p1 → p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207442702076133728989468333798 : (((p3 ∨ ((False ∧ p4) → p1)) ∨ True) → (p1 ∨ ((p5 ∨ True) ∨ ((p5 ∨ (((p1 ∨ p5) ∨ (p1 ∧ p3)) ∨ False)) → ((p3 ∧ p3) → False))))) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111837133266328509686022089815 : ((((((p1 → (p3 ∨ ((p5 ∧ p5) → p5))) → (False ∨ p3)) ∧ (p4 ∧ (p2 → (p2 ∧ p2)))) ∨ ((p4 → True) → True)) ∨ p5) ∨ (p1 ∨ p2)) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_862041572563995574136472773071 : (((((((p1 ∧ (((p2 ∧ True) → ((True ∧ p5) → p4)) ∨ (p3 ∧ (p4 ∨ p3)))) → p2) ∨ p2) ∨ ((p4 ∧ (p2 ∨ p2)) → p2)) → False) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∧ (((p2 ∧ True) → ((True ∧ p5) → p4)) ∨ (p3 ∧ (p4 ∨ p3)))) → p2) ∨ p2) ∨ ((p4 ∧ (p2 ∨ p2)) → p2)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- One of the premise coincides with the conclusion.
      exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304079854038312338348147707810 : (p1 ∨ ((p4 ∨ (((p5 ∨ (((p4 ∨ ((p5 ∨ ((True ∨ (False ∨ p4)) ∧ ((p5 → False) ∧ p2))) ∧ p3)) ∨ True) ∨ True)) → p5) → p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178922358840903970236452725681 : (((p2 → p4) ∧ ((p3 → (p3 → (p5 ∨ True))) → ((False → p3) ∨ False))) ∨ (p3 ∨ ((p4 ∨ (p2 ∨ ((False ∧ p1) ∧ p3))) ∨ (True ∨ p1)))) := by
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
theorem thm_5_vars_111291500089531235493653634796 : (((True ∧ (((True → (((p2 ∨ p4) → True) ∨ (p1 ∨ (p3 → p5)))) → ((True ∧ (p5 ∨ (False → p5))) → p1)) ∧ False)) ∧ p3) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114594023507993875882953644707 : ((((True ∧ False) → ((p3 → False) → ((p3 ∨ (p2 ∨ (p1 → p5))) ∧ (p4 ∨ p1)))) ∧ (p5 → ((p4 ∨ (p1 ∧ p2)) ∧ False))) ∨ (p1 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48677631553790248206846243364 : (((((p2 ∨ ((False → p5) ∨ (p4 ∧ p3))) ∧ (p2 ∨ p5)) ∨ (((p2 ∧ (p2 ∧ p4)) ∧ (p1 → True)) ∧ p5)) ∧ (p2 → (p4 ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703321308523731249139607223278 : ((((p5 ∧ (False ∧ (((True ∧ p2) ∧ False) ∧ (p4 ∨ p2)))) ∨ (((((True ∧ ((p1 → p2) ∨ p2)) ∨ (True ∨ p5)) ∧ p3) ∧ p1) ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69139852048520476279600452681 : ((p5 → (((((p2 ∨ p3) ∧ (p1 → p5)) ∨ ((p5 ∧ (((p4 ∧ False) ∨ (p5 → p5)) ∧ True)) → p3)) ∧ p3) ∨ (False → (True ∧ p4)))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230901816756526028833090384090 : (((p2 ∧ p3) ∨ p4) → (((p3 ∧ p4) ∨ (((p3 ∧ ((p5 → p1) → p1)) ∧ p5) ∨ True)) ∧ (((False → p1) ∧ True) ∧ ((False ∨ p3) ∨ True)))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- False on the left can always be used.
  apply False.elim h6
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44313527553927538172212341227 : ((((((p2 → (p2 ∨ (p1 → p2))) ∨ ((p5 ∧ (p3 ∧ p4)) ∧ p1)) ∨ (p5 ∧ False)) ∨ (((p1 ∨ p5) ∨ (p2 ∨ p3)) ∧ True)) → p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115148360128109707232601395180 : (((False ∨ (p3 → (((p3 ∨ ((p5 ∨ False) ∧ True)) ∨ True) ∨ True))) → ((((p1 → (p1 ∨ p2)) ∨ (p5 ∨ False)) → False) → p1)) ∨ (False ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : ((p1 → (p1 ∨ p2)) ∨ (p5 ∨ False)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h5
    -- False on the left can always be used.
    apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60124217256248493803214113725 : (((p3 ∨ p5) → (True ∧ (p4 ∧ (((p3 ∧ p5) → False) ∨ (((p4 ∧ (p5 → (p2 → True))) → (p4 ∨ p1)) ∨ (False → (False ∨ False))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_161179594367211358797906716655 : (((False ∨ p1) ∨ ((p3 → (p1 ∧ ((False ∧ p2) ∧ True))) ∨ ((((p1 → p3) → p3) ∧ p4) ∧ True))) → ((p1 ∨ p2) ∨ ((p5 ∨ p3) ∨ True))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64352593194800014546978832459 : ((p1 ∨ (((p4 → (((p1 → p2) ∨ ((p4 ∨ p3) ∨ ((p2 ∧ True) ∨ p4))) → ((p1 ∨ (p5 → (p2 → True))) ∨ True))) ∨ True) ∨ p2)) ∨ p1) := by
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
theorem thm_5_vars_339143264807475004561261682531 : (p1 → (p1 ∧ (((p5 ∧ (False ∨ (p5 ∨ p1))) → p2) ∨ (((p2 ∨ (((p4 ∨ (True → (p3 → p3))) ∧ p3) → True)) → p5) ∨ (True ∨ p5))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313108092419110921149471240451 : (p3 ∨ ((((p3 ∧ (((((p4 → p1) ∨ (False ∧ (p2 ∨ p5))) → p3) → p2) ∧ (p3 ∧ (p1 ∧ p5)))) ∧ p5) ∨ ((False ∧ p1) → p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_118156361433884322072391190419 : ((False ∨ (((p5 → p5) ∧ (p1 ∨ p1)) ∨ ((p2 ∨ p3) ∨ ((True → (True ∨ (p5 ∨ ((True → (p4 ∨ p5)) → True)))) ∧ p3)))) ∨ (p4 → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_126637141790857803227756555985 : ((p3 ∧ (p4 ∧ (p1 ∨ ((p3 ∨ (((False ∨ (False → False)) → ((p1 → p1) → p4)) ∨ (p5 ∧ (p3 ∧ p3)))) ∨ (p1 ∧ p2))))) → (False ∨ True)) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h10 =>
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
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38990737682041760723020820173 : ((((True ∨ p1) ∧ ((p2 ∨ p4) ∧ (False ∧ ((p2 ∧ (((p5 ∨ p1) → p4) → (p3 → False))) ∨ ((p2 ∧ (p3 ∧ p1)) → False))))) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135323093864700931197549551528 : ((((((p1 ∨ p3) ∨ (p2 ∨ (p5 ∧ (False ∧ False)))) ∨ p4) ∧ (((p4 → p3) ∧ p1) → p4)) ∧ ((False ∨ p3) ∨ p1)) ∨ ((p4 ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37203959756973719477151602267 : (((((p4 → (p1 ∨ (p3 ∨ p2))) ∧ (((False ∧ p2) ∧ (p5 ∧ ((((p1 ∨ p5) ∧ p2) ∧ False) → p4))) ∨ (False ∧ p2))) ∧ True) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_806747657538166338351442104733 : (((p4 → ((p1 ∧ (p2 ∨ (p5 ∨ ((((p2 ∨ (p5 ∧ p4)) → (p3 ∨ p3)) ∧ (p2 ∧ ((p1 → p1) ∧ True))) → p1)))) ∧ (p5 ∨ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_609857194193693903502420663428 : (((((p1 → ((((True ∧ p4) ∧ (False ∨ (True ∨ p4))) ∧ p4) ∨ ((((p4 → p3) ∨ (False ∧ p3)) → p4) ∨ (p4 ∨ p1)))) ∨ p1) ∨ False) ∨ p4) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64471501234591119638975128144 : ((p1 ∨ (((p5 ∨ ((p4 → True) → ((False ∨ p4) ∧ (True ∨ ((p1 ∨ (p1 ∨ p3)) → p2))))) ∧ (False → False)) → (p5 ∧ (p1 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_340896002260728168147340671676 : (p2 → ((((p3 → ((p2 ∧ (((p4 ∨ p4) ∧ p5) → False)) ∧ p4)) → p3) ∨ ((((p4 ∨ (p5 → True)) → p5) ∧ p5) ∨ (False ∨ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_153311487649326277379726830408 : ((p1 ∨ ((p5 ∨ (False ∧ p2)) ∧ ((((p4 → (p2 ∨ True)) ∨ (p5 ∨ p1)) ∧ ((p3 ∨ False) ∨ p3)) → p3))) → ((p4 ∨ (p2 ∨ p1)) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- False on the left can always be used.
      apply False.elim h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164553799354978714258040523382 : ((((((p2 → p3) → p4) ∧ (p1 ∧ p2)) ∨ (False ∧ ((True → p5) ∧ (True ∧ p3)))) ∧ p1) ∨ ((p2 → p5) ∨ (((p5 → p5) ∨ p3) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48927061985798933267144448699 : ((((((False ∨ p1) → (False ∨ (((False → (p1 → p3)) → (p3 ∧ ((p4 ∧ p3) ∨ p2))) → p2))) → False) ∧ False) ∨ ((False → False) ∨ p2)) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115770213653491915549160782648 : (((p1 → ((True ∨ (False → p2)) → p2)) → ((p5 → (p3 ∨ (((p1 → p1) ∨ p4) ∧ False))) ∧ (((p1 ∧ True) ∧ p2) ∧ p5))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_141538971607089960490558874938 : (((False ∧ (False → p2)) ∨ ((p4 → (p3 ∧ p1)) ∨ (p5 → (((p1 → False) ∨ p2) ∧ ((p1 → p5) → (p4 ∨ p1)))))) → ((p3 ∧ p4) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_306186159118266481802168841278 : (p1 ∨ ((False ∨ (p2 ∧ True)) ∨ (p1 ∨ ((((((((p3 ∨ p1) ∧ p5) → p5) ∨ (p2 ∨ ((p2 → False) ∨ True))) ∧ False) ∨ True) ∨ p3) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_173497318677020551564082170732 : ((((p5 → ((p3 ∨ (((p4 ∨ p1) → (False → True)) → p4)) ∨ True)) → p3) ∧ p2) → (p3 ∧ (p5 → (((p5 → (p5 ∨ False)) ∨ p3) ∨ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 → ((p3 ∨ (((p4 ∨ p1) → (False → True)) → p4)) ∨ True)) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314948150897914920309752542416 : (p3 ∨ ((((((True ∧ p2) → True) → p4) ∨ (p2 ∨ p3)) → False) → (p4 → (((p5 ∧ False) → (p4 → (p1 ∨ (p5 → True)))) ∧ (p1 ∧ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- False on the left can always be used.
  apply False.elim h6
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h7 : ((((True ∧ p2) → True) → p4) ∨ (p2 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h9 := h1 h7
  -- False on the left can always be used.
  apply False.elim h9
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h10 : ((((True ∧ p2) → True) → p4) ∨ (p2 ∨ p3)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h12 := h1 h10
  -- False on the left can always be used.
  apply False.elim h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_204381610008055639143702541011 : (((p5 ∨ ((False → p2) → True)) ∧ p4) ∨ ((((True ∨ p3) ∨ True) → ((p4 ∧ (p1 → (p1 ∧ p5))) ∨ (False ∨ ((p3 → p1) ∨ True)))) ∨ p5)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56385809457676234692194025747 : (((((p4 → p4) ∨ p5) → p1) → (((p5 ∧ ((p2 ∨ p4) ∨ p4)) → (((p2 ∨ (p1 ∨ p2)) → False) ∧ ((p5 ∨ False) ∧ p5))) ∨ p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 → p4) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328170954989928586703494055785 : (True → ((((p2 ∧ ((((p2 ∧ (p2 ∨ p2)) → ((False → p3) → False)) → p1) → p5)) ∧ (p2 ∧ (p3 ∨ False))) → p4) → (p1 ∨ (False → True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111488223804150891216745795646 : (((p2 → (p5 ∨ ((((False ∨ True) ∧ (((p4 ∧ (True → (p4 ∧ (p4 → (p5 ∨ p5))))) → p5) ∨ True)) ∧ p1) → p4))) ∧ p1) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200399163092705697889131745881 : (((p2 ∧ p4) ∨ ((p2 ∧ (p5 → p2)) ∧ p1)) → ((((p2 ∧ ((p2 ∧ p3) ∧ ((p3 ∧ p2) ∨ (p3 ∨ (p5 ∧ False))))) ∨ p2) ∨ p1) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Conjunctions on the left can always be decomposed.
    let h3 := h2.left
    let h4 := h2.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190478510580159939136694923631 : ((((p4 ∧ (((p4 ∧ p3) ∧ p2) ∨ p2)) ∧ p2) → p3) ∨ ((p1 ∧ (((p4 ∨ p2) → p3) ∧ ((False ∨ (True ∨ p2)) ∧ False))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119547798017603622473988195959 : ((p5 → (((((p1 ∨ ((p5 ∧ ((p4 → False) ∧ (p4 ∧ (p3 → p5)))) → p1)) → True) ∨ True) → p3) ∧ (p4 ∧ (p4 ∨ p3)))) ∨ (p4 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166962444812197769477035816558 : (((p1 ∧ (((p2 ∧ ((True → p3) → ((p4 ∧ (p5 ∨ p5)) → p1))) → False) ∨ p3)) ∧ p5) → ((p4 ∨ ((p3 → False) ∧ (p5 ∧ p5))) ∨ True)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136554607705051387216261588536 : ((((p4 ∧ p2) ∨ False) ∨ ((((p1 ∧ p2) ∨ p2) ∨ p2) → (((p5 → p5) → (((False ∨ p2) → p3) ∨ False)) ∧ p1))) ∨ ((p1 ∧ False) → p4)) := by
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
theorem thm_5_vars_257868534605218900262806383652 : ((p4 ∨ True) → ((((((p1 ∨ (False ∧ p1)) → p1) ∨ ((False ∨ p1) ∧ True)) ∧ p2) → (p2 → (p4 → (p5 ∧ p2)))) ∨ ((p1 → p1) → True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190136120128704933651762901369 : ((((True → True) ∧ ((p3 ∨ p1) ∨ (False ∨ p4))) ∧ False) ∨ (((False → p4) ∧ False) ∨ ((p1 ∧ ((p4 ∨ (p2 ∨ (True → p5))) → p3)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64721179566944852161232791286 : ((p1 ∨ (p4 → (((p4 → (p4 ∨ (p5 ∧ p4))) → ((False → (((p2 → ((p5 ∧ p5) → (p3 → True))) ∨ p2) ∧ p5)) ∧ p4)) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218409768055521242480534135507 : (((False ∧ p3) → (p5 → False)) → (((p3 → p4) → p3) ∨ (False → ((p2 ∨ p1) ∧ ((True → (p5 → (p3 ∨ (True → (p1 ∨ False))))) → p2))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_189762644319175655796472243749 : ((p5 ∨ ((p2 → (p3 ∨ p2)) ∨ (p1 → (p1 → p5)))) ∧ (p5 → (((False → p2) ∧ (((p2 ∨ p3) ∨ ((p2 ∧ p2) ∧ p2)) ∨ p4)) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1680730104609244702022113892 : ((True → (((False ∧ ((p3 → (True ∧ (p5 ∨ (p2 ∨ p1)))) → ((p1 ∧ True) → p4))) → p3) → ((False → p3) ∧ p3))) → (p1 ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((False ∧ ((p3 → (True ∧ (p5 ∨ (p2 ∨ p1)))) → ((p1 ∧ True) → p4))) → p3) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- False on the left can always be used.
    apply False.elim h6
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h8 := h3 h4
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_230554976749188016646559523594 : (((False → p5) ∧ True) → ((p5 ∧ p1) → ((p1 → False) ∨ ((((p5 → p2) ∨ (p1 → ((p4 ∧ True) → (p5 → p2)))) ∨ False) → (p4 ∨ True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h11 =>
    -- False on the left can always be used.
    apply False.elim h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767042217912599386998311985410 : (((p4 ∧ (p2 → ((p1 ∨ (((p4 → True) → p5) ∨ p1)) ∨ (((False → (p1 ∨ False)) ∧ (p5 ∧ ((p3 ∨ (p1 → True)) → True))) ∧ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54832598840534445869472123499 : (((p2 → ((p3 ∧ (p2 ∧ p1)) ∨ (True → False))) → (p3 → (p4 → ((p1 ∧ ((p4 → p1) → (((p1 ∨ p2) ∧ True) ∨ p5))) ∧ True)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_234368634768261340533386491680 : ((p1 → (p4 ∨ p1)) → ((p3 ∨ ((p5 → (p1 → ((p2 → p4) → p4))) ∨ ((((True → p1) → (p4 → (p5 → p1))) ∨ True) ∧ True))) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_653232263554241636434305530667 : ((((p1 → (True ∧ ((p5 ∧ p2) ∨ (((p2 → p4) → (False → (((p2 ∨ (p2 ∧ (p1 → False))) ∧ False) → p2))) → False)))) ∧ (p2 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313162669242074242930701404329 : (p3 ∨ (((p2 → (True ∨ ((False ∨ True) → (p3 → ((p5 ∨ p4) ∨ p5))))) → (True ∧ ((p5 ∨ (((p2 ∧ p1) → False) → p1)) → p3))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172307096672175681015554672181 : ((((p5 ∨ p4) ∧ (p2 → ((True ∨ p5) ∨ p2))) → ((False → (False → False)) → p1)) ∨ ((((False ∨ p3) ∧ p5) → p5) ∨ ((False → p2) ∧ p4))) := by
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
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- One of the premise coincides with the conclusion.
    exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62504590045739557692846804949 : ((p3 ∧ (p2 ∧ (((((True ∧ p3) ∧ p1) ∨ (p3 → p4)) ∧ (p4 ∨ ((p1 ∨ (p4 ∧ True)) ∧ (p1 ∨ (False ∨ (p5 ∧ p2)))))) ∧ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656868092070449725375167518239 : (((((p1 ∨ ((p1 ∧ True) ∨ False)) ∧ (((p4 → (p5 ∨ p5)) ∧ True) ∨ (False ∨ (False ∨ ((p5 ∨ (p2 ∧ p4)) ∧ p4))))) ∨ (False ∨ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208809295071033732668319284445 : ((p3 ∧ (((True ∨ False) ∨ p2) ∨ p1)) → ((p5 → ((((p1 ∨ (False ∧ (p3 ∨ p3))) ∨ False) ∧ p4) ∨ True)) ∧ ((p4 ∨ p2) → (p5 → p5)))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h6
      case inl h7 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h8 =>
        -- False on the left can always be used.
        apply False.elim h8
    case inr h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Implications on the right can always be decomposed.
  intro h11
  -- Implications on the right can always be decomposed.
  intro h12
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Conjunctions on the left can always be decomposed.
    let h14 := h1.left
    let h15 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- Disjunctions on the left can always be decomposed.
      cases h16
      case inl h17 =>
        -- Disjunctions on the left can always be decomposed.
        cases h17
        case inl h18 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
      case inr h20 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h21 =>
      -- One of the premise coincides with the conclusion.
      exact h12
  case inr h22 =>
    -- Conjunctions on the left can always be decomposed.
    let h23 := h1.left
    let h24 := h1.right
    -- Disjunctions on the left can always be decomposed.
    cases h24
    case inl h25 =>
      -- Disjunctions on the left can always be decomposed.
      cases h25
      case inl h26 =>
        -- Disjunctions on the left can always be decomposed.
        cases h26
        case inl h27 =>
          -- One of the premise coincides with the conclusion.
          exact h12
        case inr h28 =>
          -- False on the left can always be used.
          apply False.elim h28
      case inr h29 =>
        -- One of the premise coincides with the conclusion.
        exact h12
    case inr h30 =>
      -- One of the premise coincides with the conclusion.
      exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124972178881844603635212663833 : (((True → ((p3 → p3) → p2)) → ((((p1 → (False ∨ p1)) ∨ (False ∨ p5)) ∨ (p5 → (p5 ∨ (False → (False ∧ p1))))) → p4)) → (p2 ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115095688199108829059157319201 : (((p5 → (((p1 ∧ ((p3 ∨ True) → p4)) → (p2 ∧ p3)) ∨ p2)) ∨ ((p2 ∨ True) → (p1 ∧ ((p1 ∨ (True ∨ p3)) ∧ p2)))) ∨ (False → p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_739210307182456455181100893152 : ((((p4 ∧ p1) ∨ ((p4 ∧ ((((True → ((p5 ∨ ((True → True) ∧ (False ∨ p3))) ∨ (True ∧ p1))) → p1) ∧ (p5 → True)) → p4)) ∧ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264490114251639066005774957608 : (True ∧ (((p1 ∧ p3) → True) ∧ (p5 ∨ (((p4 ∧ p1) ∧ (False ∧ (p2 ∨ (True ∧ (p2 ∨ p1))))) ∨ ((p5 ∧ (p2 ∨ (p1 → p1))) → True))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58045551226190000384270008699 : (((False ∧ False) ∧ (((False → p3) → (p4 → (((True → p3) ∧ ((False → ((p5 → p5) ∨ p5)) → p4)) ∨ (p3 → (p2 ∨ p1))))) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_138865774776153486479056347441 : (((p2 ∨ (((True ∧ ((p5 ∨ False) → (False → (True ∧ (False ∧ True))))) ∧ ((False ∨ True) ∨ p1)) ∧ (p2 → p5))) ∧ p2) → ((p2 → False) → p4)) := by
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
    have h6 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h7 := h2 h6
    -- False on the left can always be used.
    apply False.elim h7
  case inr h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h9.left
    let h12 := h9.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h15 =>
      -- Disjunctions on the left can always be decomposed.
      cases h15
      case inl h16 =>
        -- False on the left can always be used.
        apply False.elim h16
      case inr h17 =>
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h18 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h4
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h19 := h2 h18
        -- False on the left can always be used.
        apply False.elim h19
    case inr h20 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h4
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h22 := h2 h21
      -- False on the left can always be used.
      apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_345356176710041660454960612794 : (p3 → (((((((p1 ∧ ((False ∧ p5) ∧ (False ∧ (True ∧ p2)))) ∧ (True ∧ p5)) ∨ False) ∨ (p5 ∧ (p2 ∧ (p5 ∨ p2)))) ∨ False) ∨ p3) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670643086195674262048516838000 : (((((True ∨ p2) → (((p5 → p3) ∨ (p5 → ((p5 ∧ p3) ∧ p3))) → ((p3 ∨ (True ∧ p3)) ∧ (False → p2)))) ∨ (p5 → (p1 ∨ True))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_58156335903015034490381985017 : (((p2 ∧ p5) ∧ (p2 ∧ (((p4 → True) → False) ∧ ((((p5 → p5) ∨ (((p1 ∧ p1) ∨ True) ∧ p1)) ∧ p4) ∧ ((True ∧ True) ∧ False))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219459276044836167602750329702 : ((p4 ∨ (p5 ∧ (p3 ∨ p1))) → (((True ∧ False) ∧ ((p5 → (((p5 ∨ True) ∧ True) → p2)) ∧ p3)) ∨ (((False ∧ True) ∨ (p1 ∧ False)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
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



