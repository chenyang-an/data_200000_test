variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133973093354696490315189524761 : ((((((((p4 ∧ p3) ∧ False) ∨ (p1 ∨ (p3 → ((p3 → ((p2 ∧ p1) ∨ p4)) ∧ True)))) ∧ p2) ∧ False) ∧ False) ∨ True) ∨ (p3 → (True ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166948663844078501978634785741 : ((((p4 → p5) ∨ (False ∨ (p4 ∨ ((p4 → (((p2 → p2) → p1) ∧ False)) ∧ p1)))) ∧ p5) → (p1 ∨ (p1 ∨ (False ∨ ((p1 ∧ p3) → p3))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- Conjunctions on the left can always be decomposed.
        let h13 := h12.left
        let h14 := h12.right
        -- One of the premise coincides with the conclusion.
        exact h14
      case inr h15 =>
        -- Conjunctions on the left can always be decomposed.
        let h16 := h15.left
        let h17 := h15.right
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52952900741490425429620277810 : (((((p2 ∨ p4) ∧ (p2 ∧ (p1 ∨ (p1 → (p3 → True))))) ∨ p2) ∧ ((((p4 ∧ p2) → False) ∨ (False ∧ ((True → p4) ∧ p5))) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305675448973104104253646977144 : (p1 ∨ (((((p1 ∧ False) ∧ p5) ∧ (p5 ∨ p1)) ∨ (False → p1)) ∨ ((((True → True) → (p3 → True)) → ((p5 → False) ∨ (False ∧ False))) ∧ True))) := by
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
theorem thm_5_vars_190435870257906240614141249656 : (((True → (((True ∨ p5) ∧ (p1 ∧ p2)) → False)) ∨ False) ∨ ((((True ∨ p1) ∧ p5) ∧ (True → p5)) → (p4 ∨ (p5 ∧ ((p2 → False) ∨ p5))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- One of the premise coincides with the conclusion.
    exact h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187469590116357460481527315068 : ((True ∨ (p4 ∨ (p5 ∧ (((p1 ∧ (p1 ∧ p1)) ∧ p1) → True)))) → (((p4 ∨ (p4 → p2)) ∨ p5) ∨ (((True → (True ∨ p5)) ∨ True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h4 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h5 =>
      -- Conjunctions on the left can always be decomposed.
      let h6 := h5.left
      let h7 := h5.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206036668381724596263296064623 : ((p2 ∧ (True ∧ (p4 → (p5 → False)))) ∨ ((p5 ∨ (p2 ∧ ((p4 → p1) ∨ ((True ∧ ((p3 → True) → False)) ∧ (False → p5))))) ∨ (True ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_228276233029840519791911715963 : ((p5 ∧ (p5 → p4)) ∨ (p4 → (True ∧ (p1 ∨ ((p5 → p4) → ((p1 → ((p2 ∧ (p4 → ((p1 → False) ∨ (p3 ∨ p2)))) ∨ True)) ∨ p2)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157714687471155876273793951825 : (((((False ∨ p4) → (p2 → (True ∨ False))) → ((p1 ∨ (True → p4)) ∨ p4)) → ((p4 ∧ False) ∧ False)) ∨ (((p5 → (p1 ∧ p4)) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314546356414311681913699531467 : (p3 ∨ ((((p3 ∨ False) → (((p4 ∨ False) ∧ p4) ∨ ((p5 → False) ∧ True))) → (False ∧ (False ∨ p4))) ∨ (p3 ∨ (p4 → ((True ∨ p2) ∨ p3))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98805451333442299626315515941 : ((True → (((((p4 ∨ p4) → ((p5 ∨ p4) ∨ True)) → (((p1 → (p5 ∧ p2)) ∧ (p5 ∧ (p5 ∨ False))) ∨ True)) ∨ (p1 → p5)) ∧ False)) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- False on the left can always be used.
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308611729506896233846837709786 : (p2 ∨ (((p5 → True) ∧ (p3 ∨ (p4 ∨ ((p5 ∨ ((p2 ∨ False) → (p1 ∨ ((p2 ∨ (((p1 ∨ p2) ∨ p1) ∧ p1)) ∧ True)))) ∨ True)))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181069641905822243316793362587 : (((False ∨ p5) → (True ∧ (p1 ∧ (p3 ∨ (p1 → (p1 ∧ (p3 ∨ p4))))))) → ((True → (((p5 ∧ p1) ∧ True) ∧ (False → (p1 ∧ p2)))) → p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the left conjuct of h5 based on <expert-advice>.
  let h6 := h5.left
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164965624237674782896073980857 : (((((p2 → (p5 ∨ True)) ∨ (((p3 → (p4 → p2)) ∧ p2) ∧ p5)) ∧ (True ∨ True)) → p1) ∨ (True ∨ (((p3 ∨ (p5 ∧ p4)) → p5) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727595530211778554734512657609 : ((((p5 ∧ (True ∨ p3)) ∨ (True ∧ (p3 ∧ (p4 ∨ ((p5 → ((False ∨ (p5 ∧ p1)) → p4)) → ((p5 → ((True ∨ p2) → p3)) ∧ p5)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_174590239140352865681810218974 : ((((p1 ∧ (p1 ∨ p4)) → True) ∨ ((True ∨ (False → (p5 → (p3 ∧ p5)))) ∨ p1)) → ((p3 ∨ ((False ∨ (p1 ∨ p4)) → (p3 → p1))) ∨ True)) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
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
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190396128475866328399439381973 : (((p2 ∧ (((p4 → (p1 ∨ p1)) ∨ p1) → False)) ∨ True) ∨ (((p4 ∨ p5) ∧ ((((p5 ∧ p5) ∨ p1) ∧ (p4 ∨ (p5 → p1))) ∨ False)) ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185303903717920575987697338915 : ((p2 ∧ (p2 → ((False ∧ ((p3 ∨ p4) → False)) ∧ (p1 ∨ False)))) ∨ ((p5 ∨ (((True ∧ p5) ∨ (p2 → False)) → (p4 → (p1 ∧ p2)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178036518462923692862889775014 : (((((((p5 ∧ p4) → ((True → True) ∧ p3)) ∧ p3) ∨ p4) ∧ True) → p2) ∨ (p3 ∨ ((False → (p5 → (p4 → p5))) ∨ (False ∧ (False ∨ p5))))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135590985986963841489206298775 : ((((p3 ∨ ((True ∨ p1) ∧ (p2 → (p1 ∧ (p1 ∨ p4))))) ∧ ((p5 → p1) → p2)) ∨ (True → ((True ∧ p1) ∨ p1))) ∨ (p2 → (p4 ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66256360855336582330899159129 : ((p5 ∨ ((p2 ∨ (p4 → (p4 → p5))) ∨ (((p4 ∧ False) ∨ (((p1 → True) ∧ (p3 → p5)) ∧ p5)) ∧ (((p3 ∨ p2) ∧ p3) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308528077868225870336293542749 : (p2 ∨ (((((False ∨ (p1 → p4)) ∨ ((p1 ∨ p1) ∨ ((p3 ∧ p2) ∧ p4))) ∨ False) → (((p3 ∨ p1) ∨ True) → (False ∨ (p1 ∨ p3)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_98912382902603290910074825515 : ((True → ((((p3 ∨ (((True ∨ p3) ∨ ((((p5 ∧ p5) → p4) ∨ p2) ∨ p2)) ∧ p4)) → (True ∧ (p4 ∨ p1))) ∨ p5) ∧ (p5 ∧ False))) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337103294266084561427100348383 : (p1 → ((((p4 ∧ (p5 ∧ p1)) → p1) → ((((True ∨ (p2 ∨ p5)) ∨ ((True ∨ (p4 ∨ p1)) ∧ p4)) → (p2 → p3)) ∨ p4)) ∨ (p4 → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308497763886258513211757933898 : (p2 ∨ (((((p1 → p4) ∨ ((p2 ∨ ((p5 → p5) ∧ (True → (p4 ∨ p4)))) → (p5 → p1))) ∨ p2) ∧ (((p3 → False) ∨ p4) → p1)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_703245100055882039217347425829 : ((((p2 ∧ (((p4 → (False → p5)) ∧ (p2 ∨ p2)) → p1)) ∨ (p4 ∨ (((False → (((p1 ∧ True) ∧ (p4 → p1)) ∨ p4)) ∨ True) ∨ p5))) ∨ p1) ∧ True) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307484365303470526137586536782 : (p1 ∨ (True → ((((p1 ∨ (p3 ∨ (p4 → (p3 → ((False ∧ (p5 ∨ p5)) ∨ ((False ∧ True) → (p3 ∧ False))))))) ∨ p1) ∨ (p2 → True)) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_205862822870851744561302652540 : (((p5 → False) → (p4 ∧ (p4 ∧ p4))) ∨ (((p2 → ((p1 → p4) → p1)) ∨ True) ∨ (True ∨ (((p1 → (False → (True ∨ p3))) ∧ p3) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_961859248125956846679664367129 : ((((p4 ∨ False) ∧ ((((False ∨ ((True ∧ p2) ∧ p5)) ∨ p1) → (p1 ∨ True)) ∧ (p4 → ((True ∧ (((p3 ∨ True) ∧ p1) ∨ p4)) ∧ False)))) → p2) ∧ True) := by
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
    let h5 := h3.left
    let h6 := h3.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h8 := h6 h7
    -- We need to get the right conjuct of h8 based on <expert-advice>.
    let h9 := h8.right
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_592449893624967824487956226732 : ((((((p4 ∧ (p4 → (p2 ∧ (p4 ∨ p3)))) → ((((((p4 ∧ (False ∧ p2)) → p1) ∨ p5) ∧ p2) ∧ True) → True)) → (p3 → p5)) ∧ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305682661417462280287245336181 : (p1 ∨ (((p3 → p1) ∧ (((p4 ∧ (p3 ∨ p3)) ∨ False) ∨ p3)) ∨ ((False ∧ p4) → ((p2 → p5) ∨ (False → (((True ∧ p4) ∨ p3) → p5)))))) := by
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
theorem thm_5_vars_336687562899120523798430565456 : (p1 → (((p1 → (((True ∨ (((p2 → True) → p1) ∧ p3)) ∨ (p4 → p4)) ∧ p4)) ∧ (p4 → (((p3 ∨ p3) ∧ p1) ∧ (False ∧ p1)))) → p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254584928191125272639728840096 : ((p3 ∧ p1) → (((((p5 → p1) ∨ (True ∨ (p1 ∧ p4))) → ((((p3 → p2) ∧ (True ∧ (p5 ∨ p3))) ∧ False) ∨ False)) ∨ p1) ∨ (p3 ∧ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40124068565592097989738355104 : (((((False ∨ ((p4 ∨ (p2 ∧ (False ∧ p1))) ∨ (p5 ∨ (((True → (p2 → p4)) ∨ p5) ∧ p2)))) ∧ ((p4 → False) → False)) ∧ False) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_671227066988556018046859642897 : ((((p4 ∨ ((((((p1 → ((p4 ∧ ((p1 → p1) ∨ (p3 → p2))) ∧ p1)) ∧ p3) → p5) → False) ∨ p4) ∨ True)) ∨ (p4 ∧ (p1 ∨ p1))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_720569391319670873066446941000 : ((((((False ∧ p4) ∧ True) → p3) → (p2 ∧ (((((p3 → ((True → p2) → ((p5 → p1) ∨ p3))) ∧ (p5 ∨ p3)) → p3) ∨ True) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_642906208208665266963455033613 : ((((p2 ∧ ((p3 ∧ (((p2 ∧ ((p4 ∧ p3) ∧ p1)) ∨ ((False ∧ p1) ∧ ((p4 → p1) ∨ (p4 → p3)))) ∨ p2)) ∨ (p1 → p2))) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_722236918636731408478221084193 : ((((p5 → (True → (p1 ∧ p5))) → (p3 → ((((p1 → True) ∨ p4) → ((((p5 ∧ p5) ∧ p5) ∧ (p3 ∨ p5)) ∨ (True → p4))) → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_610878420716691209549115318152 : (((((((p5 → False) → ((p2 ∧ (True ∧ p3)) ∧ ((True → p1) ∨ p2))) ∧ (((((p3 ∧ False) → p5) ∧ p5) ∧ p3) ∧ p2)) → p4) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_247641556234629230599792250697 : ((False ∨ p5) ∨ (p4 → ((((True ∧ (((((p4 ∧ p5) ∧ True) ∧ ((False → (p2 → False)) → False)) → p2) → p1)) ∧ (p1 → p1)) → p2) ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227525746281101008419301593826 : ((True ∧ (p5 ∨ p1)) ∨ (True ∧ (p3 ∨ (((p5 ∨ ((p1 ∧ ((p1 → ((p5 ∧ (False ∧ p1)) → p3)) ∨ True)) ∨ True)) ∨ (p2 ∨ p2)) ∨ p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_50616958162115503904454851402 : ((((((p4 → ((p1 ∧ p1) ∧ ((p1 → p5) → p2))) ∧ (True ∨ False)) ∨ True) ∧ ((p1 ∧ True) → p5)) → ((p4 ∨ p5) ∨ (True ∧ True))) ∨ False) := by
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
    let h5 := h4.left
    let h6 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- False on the left can always be used.
      apply False.elim h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_561284255428765312829123921812 : (((p4 ∨ (p1 → (((p4 → ((p2 ∧ p1) ∧ True)) → ((((p4 → p1) ∧ ((p5 ∨ p1) → ((p1 → False) ∧ False))) ∧ p3) → p4)) ∧ True))) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h4.left
  let h7 := h4.right
  -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
  have h8 : (p5 ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h7, we can now drive its conclusion.
  let h9 := h7 h8
  -- We need to get the right conjuct of h9 based on <expert-advice>.
  let h10 := h9.right
  -- False on the left can always be used.
  apply False.elim h10
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_693089705298154588896736033343 : ((((p2 ∧ (((p3 → ((p5 ∨ p3) → True)) → p5) ∧ (True → (False ∧ p5)))) ∧ (p3 ∨ (False ∧ (((p5 ∧ False) ∧ p3) ∧ (p4 → True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_746168135671359922601569297312 : ((((p1 ∨ p2) → (False ∨ (p2 → (((p1 → (p4 → p1)) ∧ (p2 → False)) → (((True ∨ (p4 → False)) ∨ p5) → (p2 → (p4 ∧ True))))))) ∨ False) ∧ True) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Conjunctions on the left can always be decomposed.
        let h9 := h4.left
        let h10 := h4.right
        -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
        have h11 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h10, we can now drive its conclusion.
        let h12 := h10 h11
        -- False on the left can always be used.
        apply False.elim h12
      case inr h13 =>
        -- Conjunctions on the left can always be decomposed.
        let h14 := h4.left
        let h15 := h4.right
        -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
        have h16 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h3
        -- We have shown the premise of h15, we can now drive its conclusion.
        let h17 := h15 h16
        -- False on the left can always be used.
        apply False.elim h17
    case inr h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h4.left
      let h20 := h4.right
      -- We want to use the implication h20 based on <expert-advice>. So we show its premise.
      have h21 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h3
      -- We have shown the premise of h20, we can now drive its conclusion.
      let h22 := h20 h21
      -- False on the left can always be used.
      apply False.elim h22
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h23 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h24
    -- Implications on the right can always be decomposed.
    intro h25
    -- Implications on the right can always be decomposed.
    intro h26
    -- Implications on the right can always be decomposed.
    intro h27
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Disjunctions on the left can always be decomposed.
    cases h26
    case inl h28 =>
      -- Disjunctions on the left can always be decomposed.
      cases h28
      case inl h29 =>
        -- Conjunctions on the left can always be decomposed.
        let h30 := h25.left
        let h31 := h25.right
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h32 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h33 := h31 h32
        -- False on the left can always be used.
        apply False.elim h33
      case inr h34 =>
        -- Conjunctions on the left can always be decomposed.
        let h35 := h25.left
        let h36 := h25.right
        -- We want to use the implication h36 based on <expert-advice>. So we show its premise.
        have h37 : p2 := by
          -- One of the premise coincides with the conclusion.
          exact h24
        -- We have shown the premise of h36, we can now drive its conclusion.
        let h38 := h36 h37
        -- False on the left can always be used.
        apply False.elim h38
    case inr h39 =>
      -- Conjunctions on the left can always be decomposed.
      let h40 := h25.left
      let h41 := h25.right
      -- We want to use the implication h41 based on <expert-advice>. So we show its premise.
      have h42 : p2 := by
        -- One of the premise coincides with the conclusion.
        exact h24
      -- We have shown the premise of h41, we can now drive its conclusion.
      let h43 := h41 h42
      -- False on the left can always be used.
      apply False.elim h43
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246144699434432850500392430953 : ((p4 ∧ p2) ∨ ((p5 ∨ (p5 → (p1 → (((p1 ∧ (True ∨ ((p5 ∨ (p2 ∧ p5)) ∨ p1))) → p4) → ((p4 ∧ p3) ∨ p1))))) ∨ (False ∨ p3))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_635044343224602687877145671292 : ((((((False ∨ ((p3 ∨ (False → ((((p1 ∧ True) → p1) ∧ (True ∧ p4)) ∧ (p2 → False)))) ∧ p4)) → p3) → ((True ∧ p2) → p5)) → False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318741523293596972801427780116 : (p4 ∨ (((p5 → p2) ∨ (((p5 ∨ p4) ∨ ((False ∧ True) ∨ False)) ∨ (p1 ∨ (((p4 ∨ (p1 ∧ (p3 ∧ p5))) → p5) → p5)))) → (p5 ∨ True))) := by
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
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h5 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h6 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Conjunctions on the left can always be decomposed.
          let h10 := h9.left
          let h11 := h9.right
          -- False on the left can always be used.
          apply False.elim h10
        case inr h12 =>
          -- False on the left can always be used.
          apply False.elim h12
    case inr h13 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118592055391677532104907703670 : ((p4 ∨ ((p3 ∨ (p5 ∨ (p5 ∧ ((p2 ∧ ((((p2 ∨ p4) ∧ p1) ∨ p2) ∨ p2)) ∨ ((p1 → (p5 → p4)) ∧ p1))))) → p3)) ∨ (p2 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_781551497263575744587177963919 : (((p2 ∨ (False ∨ ((p2 ∧ (p4 ∧ (((((p4 → (True ∧ False)) ∧ p1) ∧ (p1 → ((False → False) → False))) ∧ p1) ∧ (p5 ∨ p3)))) ∨ True))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324396329776932874642215129935 : (p5 ∨ (((p3 ∧ (p5 → (p3 ∨ p2))) ∨ False) → (((p5 ∨ p3) → ((p1 ∧ (p5 → p1)) → ((p3 → ((p1 ∨ p5) → p3)) → p5))) ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168322883584235786724577067404 : (((p2 → False) ∧ (p1 → ((p1 → p3) ∨ ((p4 → (False ∨ ((p5 ∨ p3) → False))) → p5)))) → ((((p3 ∧ False) ∨ p4) ∨ p5) ∨ (p2 → False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h5 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h4
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h5
  -- False on the left can always be used.
  apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328123990624725085448089123897 : (True → ((((p2 → p4) ∧ ((p2 ∨ (p4 → p3)) ∧ p5)) ∨ ((p3 → (p3 → True)) ∧ ((p1 ∨ False) ∨ (p5 → p2)))) ∨ (True ∨ (p4 → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39531847863657040119516812979 : (((False ∨ (((p3 ∧ (p4 ∧ (p4 ∧ True))) ∨ True) → ((((p4 → p2) → (p3 → (p1 ∧ True))) ∧ (False ∨ (True ∧ False))) ∨ p3))) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_163762635595763121397126951465 : ((True ∧ ((((p3 ∨ p5) ∨ (((False ∧ p5) → ((p3 ∨ p2) → p1)) ∨ True)) ∨ p3) ∨ p2)) ∧ (p1 → ((((p3 ∨ p3) ∧ p5) → p2) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_729712385777816292665466497117 : (((((p2 → p1) ∨ p5) → ((p1 → ((((p4 ∧ (p5 ∨ p1)) ∨ False) ∧ (True ∨ (True ∨ p1))) ∨ (p2 → (p1 → (p3 → p2))))) ∨ p1)) ∨ p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Implications on the right can always be decomposed.
    intro h4
    -- Implications on the right can always be decomposed.
    intro h5
    -- Implications on the right can always be decomposed.
    intro h6
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h8
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h9
    -- Implications on the right can always be decomposed.
    intro h10
    -- Implications on the right can always be decomposed.
    intro h11
    -- One of the premise coincides with the conclusion.
    exact h9
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1567337332350735731479733556 : ((p2 → (((((p1 ∧ p5) ∧ ((((p4 ∨ (p1 → False)) ∧ p2) ∧ p5) ∧ True)) ∨ True) ∧ p2) ∨ (False → (p2 ∨ p5)))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134723675416430218217990924859 : (((((True ∨ p2) ∧ p5) → ((False ∧ (p1 → p4)) ∧ ((p3 → ((p1 ∨ (p2 ∧ (p5 ∧ p4))) ∧ p1)) ∧ p4))) → p2) ∨ (p1 → (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_110706009206864253847330078574 : ((((((p2 ∨ (((p5 → ((p1 → ((True ∨ p4) → p2)) ∧ p1)) → True) ∧ p2)) ∨ (False → (p4 → False))) ∨ p4) ∧ False) ∧ p3) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251164309623749397526139416345 : ((p2 → False) ∨ (p4 → ((False ∨ True) ∧ (((p3 ∧ ((p5 ∧ p3) → (p1 ∨ p2))) → (p5 ∨ (False ∧ (p5 → p1)))) ∨ ((p3 → p3) → p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_87461069048939807131409177544 : (((p4 → ((p2 ∧ (p4 → p5)) → False)) ∧ (((p2 → p2) → ((p4 → (False ∨ ((p1 ∨ (p2 → True)) ∨ (p4 → p2)))) ∧ p4)) ∧ p2)) → p4) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h6 : (p2 → p2) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h8 := h4 h6
  -- We need to get the right conjuct of h8 based on <expert-advice>.
  let h9 := h8.right
  -- One of the premise coincides with the conclusion.
  exact h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22966129948497545794964787325 : (((p3 ∨ (p5 ∧ (True ∧ (p1 ∨ p2)))) ∨ ((False ∨ True) ∧ ((p4 ∧ (p4 → (p2 ∨ (p3 ∧ (p1 ∨ p3))))) → ((p4 ∨ p4) ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254015754461822709403225122729 : ((p1 ∧ p5) → (p1 → (((((p1 → p5) → (p5 → (p5 → (p3 ∧ ((p3 → (True ∧ p2)) → (p2 ∧ (False ∧ True))))))) ∧ p5) ∨ p5) ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64289629095907015162221925877 : ((False ∨ (p3 → (((((p1 → (p2 → (((p2 ∧ p3) → False) → (p2 ∧ p2)))) → (p2 ∨ (p4 ∨ True))) ∧ (p5 ∧ False)) ∧ p5) ∨ p2))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51022014460684785786961480557 : (((p2 ∧ ((p2 ∨ p2) → ((False → ((p3 → True) ∨ (True → (True ∨ p1)))) ∧ (p1 → False)))) ∧ (((p2 ∨ (p4 → p5)) → p2) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_631999756131570017309524695506 : ((((((p5 ∧ (p4 ∧ p3)) ∨ (((p1 → p2) ∧ False) ∨ (((True ∨ p2) ∨ ((((p5 ∧ p3) → False) → p5) ∧ p4)) ∨ p3))) → p1) → p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115734319486910515881169464976 : ((((p1 → (True ∨ p2)) ∨ (p3 → p5)) → ((((p4 ∨ (p3 → False)) ∧ p5) ∨ p2) ∨ ((((p4 → p2) → p3) → True) ∨ p4))) ∨ (p5 ∨ p1)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727509248619116266407711099913 : ((((p4 ∧ (p4 ∧ False)) ∨ (((p3 → p2) ∧ ((p3 → p2) ∧ (((p1 → p4) → ((p2 → p3) → p2)) ∨ (p3 ∨ p5)))) ∨ (p4 → p1))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116273288908893938829797266658 : (((p5 ∧ (p4 ∨ p2)) ∨ ((True → (p4 ∨ (False ∧ p3))) → (((((False ∧ False) → (p5 → p4)) ∧ (p3 ∨ p5)) → p4) ∧ True))) ∨ (p4 → p5)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h7 := h1 h6
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- False on the left can always be used.
      apply False.elim h10
  case inr h12 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h13 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h14 := h1 h13
    -- Disjunctions on the left can always be decomposed.
    cases h14
    case inl h15 =>
      -- One of the premise coincides with the conclusion.
      exact h15
    case inr h16 =>
      -- Conjunctions on the left can always be decomposed.
      let h17 := h16.left
      let h18 := h16.right
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186224900297291497782217647556 : (((p2 → ((p5 ∨ p5) ∨ (((p1 → p5) ∨ p3) ∧ p5))) ∨ False) → ((((((((False → p5) ∨ p1) ∧ p1) ∨ p4) → p1) → True) → False) ∨ True)) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707100952285096843526555374291 : (((((((p5 ∧ (p3 → False)) ∨ p5) → p5) → False) ∨ (p1 ∨ (((((p1 ∨ False) ∨ True) ∨ (p5 ∧ p4)) ∨ (p5 → p3)) ∧ (False → p3)))) ∨ p4) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_147546783008856311542083745060 : (((p4 → (((p3 → p2) → (((False ∨ (p2 → p2)) ∨ ((p3 → p2) → p3)) → (True ∧ False))) ∨ True)) ∨ p2) ∨ ((p3 → False) ∧ (p1 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300886104412124610848615133816 : (False ∨ ((p2 ∧ ((p5 → (False ∧ ((p5 ∧ p1) → (False ∨ p5)))) → (p1 ∧ False))) ∨ (p5 ∨ ((True ∧ ((p4 ∧ False) ∨ (False → p1))) ∨ p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711002429577726848298725884728 : (((((True ∨ p1) → (True ∧ (True ∨ p4))) ∧ ((p1 ∨ ((((False → p4) ∨ False) → ((p2 ∧ True) ∧ (False ∨ p1))) ∨ (p4 ∧ p5))) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114060831626704962007280346453 : ((((((p4 ∨ p2) ∨ False) ∧ (((p1 ∧ p4) ∧ False) → True)) ∧ (p4 ∨ (p2 ∨ (False → (p4 ∨ False))))) ∨ ((p2 ∨ False) → p2)) ∨ (p3 ∧ False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323570669282174989211931481801 : (p5 ∨ ((((p4 → (p2 ∨ p3)) ∧ p5) ∨ (p4 → ((((p5 → p3) ∧ ((p4 → p3) ∧ (p1 ∨ p5))) ∨ True) ∨ True))) → ((True → False) ∨ True))) := by
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
theorem thm_5_vars_250141276317930300123921157397 : ((True → p5) ∨ (((((((False → p2) ∨ (p1 → (False ∨ p4))) ∧ p2) ∨ False) → p3) ∨ ((((True → p1) ∧ p4) → (False ∧ p1)) → True)) ∨ p3)) := by
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
theorem thm_5_vars_308646223438483665974883338625 : (p2 ∨ ((p1 ∧ (((p5 → (((((False ∨ False) ∨ True) ∧ p3) ∨ (p2 ∨ False)) → (p4 ∧ p1))) ∧ ((p1 → True) → (p4 → p3))) ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134999757386417369239353374042 : (((p3 ∧ (((p1 ∧ p5) ∧ ((p4 → ((True ∧ (p2 ∨ (p5 ∨ False))) ∨ p3)) → p5)) ∧ (False ∧ p5))) ∧ (p5 ∧ False)) ∨ (p2 → (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111215786046547634110228747275 : (((((p4 ∧ p5) ∨ True) → (((p2 ∨ (((p2 ∨ p5) ∨ (p2 → p4)) ∧ p3)) ∧ (True ∨ p2)) ∧ (p4 ∨ (p2 ∨ p5)))) ∧ p2) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42644611004295737680137833736 : (((p4 ∨ (((p4 ∧ ((((p1 ∧ (True → True)) → p3) ∧ (p4 ∧ ((False ∧ p5) ∧ p3))) ∨ True)) ∨ (True → (p5 ∨ p5))) ∧ p3)) ∨ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117823687568194245228621391731 : ((p4 ∧ (p2 ∧ (((((((False → (True → p4)) ∨ (p5 ∨ (p4 → p3))) ∨ True) ∨ p1) ∨ (True ∧ p5)) → (p4 → p5)) ∨ p2))) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113514755722467946212213196274 : (((((((False → (p1 ∧ p3)) ∨ p2) → ((p1 ∧ p5) ∧ p3)) ∨ p5) → (p1 → (((p3 ∧ p1) ∨ True) ∧ p5))) ∨ (p2 → p3)) ∨ (p4 ∧ p1)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h5 =>
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : ((False → (p1 ∧ p3)) ∨ p2) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- False on the left can always be used.
      apply False.elim h7
      -- False on the left can always be used.
      apply False.elim h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h8 := h5 h6
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- One of the premise coincides with the conclusion.
    exact h10
  case inr h11 =>
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165945658460557152137846352334 : (((p2 ∨ False) ∧ ((False → (p2 ∧ (True ∨ ((p5 → p5) → False)))) → (p1 ∨ (p2 ∨ p4)))) ∨ ((True → (p1 ∨ (True ∧ p4))) → (True ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_905423789151575379516789401 : ((p4 → (p3 ∨ (((True ∧ p3) ∨ (False ∨ ((p2 ∧ p5) ∨ (p5 ∨ p5)))) → ((p1 ∧ ((False ∨ p1) → p5)) ∨ (p5 ∨ p3))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h13
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44779804978159599617106167243 : ((((p5 ∨ ((p5 ∧ p5) → True)) → (((((p2 ∨ p1) ∧ p1) ∧ (p4 ∨ p4)) → True) ∧ (((False → True) → (p5 → True)) ∧ p1))) → p1) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p5 ∨ ((p5 ∧ p5) → True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_320084487963090898220892107714 : (p4 ∨ (((p2 → True) ∧ p1) → (p4 ∨ ((p1 → (((p3 ∨ p3) ∧ ((p2 ∧ (True ∧ ((p1 → False) ∧ p2))) ∧ p3)) ∨ True)) ∨ (p5 ∨ p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52233785957541521612481787613 : (((p2 ∧ (((p4 → False) ∨ (False → True)) → ((p4 → (p5 ∨ p3)) ∨ (False → p2)))) → ((p5 → p5) → (p3 → ((p4 ∨ p1) ∨ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_602887275862285715826545874413 : ((((p1 ∨ (((p4 ∨ (((p3 ∨ (p1 → p3)) ∧ p4) ∧ ((p3 ∨ ((p1 ∧ p1) → (p3 ∨ p1))) → p4))) ∨ p5) ∧ (p1 ∨ p5))) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51977372801199479810903065514 : ((((p5 ∧ p3) ∧ (((True ∧ (p5 → p2)) ∧ p5) → ((True ∨ True) → (p5 ∧ p1)))) ∨ (((True ∧ False) → (p5 → p1)) → (p4 ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670469145295387215361395788249 : (((((True ∨ p3) ∧ ((p1 ∧ (((p4 ∧ p4) ∧ p2) ∧ ((True ∨ p5) ∧ ((p3 ∧ p5) ∨ p3)))) ∧ (False → p4))) ∨ (False → (p4 → False))) ∨ p4) ∧ True) := by
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
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183869529146252947263912161243 : (((((p3 ∨ (p1 ∧ True)) → False) → ((p2 ∧ False) ∧ p4)) ∧ p2) ∨ ((((p3 ∧ p3) → True) → (p1 ∨ (p5 → (p2 → (p3 → False))))) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_244484410584480343115561995398 : ((False ∧ p2) ∨ (p5 → ((((((p3 ∧ p4) → p2) ∧ p3) ∧ ((True ∧ (p5 ∨ True)) ∨ (p5 → ((p5 ∧ p2) → (p1 → False))))) ∨ p2) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_168082874045666407963380646366 : (((False → (p4 ∨ (p1 ∨ p5))) ∧ (((((p1 ∧ p1) ∨ True) ∧ p5) ∨ (p4 ∧ p4)) ∧ p1)) → (((False → (p4 ∧ p5)) → False) ∨ (False → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h13 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h14
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h15 =>
    -- Conjunctions on the left can always be decomposed.
    let h16 := h15.left
    let h17 := h15.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h18
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_35058712576162963875828306169 : ((p1 → ((False ∨ (p3 ∨ (False ∨ (p4 → ((True ∧ p3) ∨ (p3 ∨ (p4 ∧ (False ∨ (False → (p3 ∧ (p2 → p1))))))))))) ∨ (p4 ∨ p5))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336469329223265088258151770903 : (p1 → ((p2 → ((((p5 ∨ p3) ∨ (((p5 → p1) ∨ (p4 ∧ (((False → (p1 → p1)) ∧ p3) ∨ True))) → p5)) ∨ (p4 ∧ p2)) → False)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158584847777803360810518719562 : ((True ∧ (False ∨ (False ∨ ((p2 ∨ p4) → ((False ∧ ((p1 → p4) ∨ (p5 ∧ p5))) ∧ (True ∨ True)))))) ∨ ((False ∧ ((p2 ∧ p3) → False)) → p2)) := by
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
theorem thm_5_vars_11508949336529383419480036286 : (((((p3 ∧ (p3 → False)) ∧ (p3 ∨ (p2 ∨ ((p5 ∨ (False → ((p4 → p5) → (p5 ∨ (p5 ∨ p5))))) → p4)))) ∧ (p1 ∨ p3)) → p1) ∧ True) := by
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
  let h6 := h4.left
  let h7 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h9
    case inr h10 =>
      -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
      have h11 : p3 := by
        -- One of the premise coincides with the conclusion.
        exact h10
      -- We have shown the premise of h7, we can now drive its conclusion.
      let h12 := h7 h11
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h15 =>
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h16 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h17 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h16
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h18 := h7 h17
        -- False on the left can always be used.
        apply False.elim h18
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h20 =>
        -- One of the premise coincides with the conclusion.
        exact h20
      case inr h21 =>
        -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
        have h22 : p3 := by
          -- One of the premise coincides with the conclusion.
          exact h21
        -- We have shown the premise of h7, we can now drive its conclusion.
        let h23 := h7 h22
        -- False on the left can always be used.
        apply False.elim h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_758141906920180170106996022935 : (((p1 ∧ (p3 → (((((False ∧ p4) → (p5 ∧ False)) ∨ p2) ∨ ((p2 → (p1 ∧ (((p5 ∧ p5) ∨ (False ∧ True)) → p3))) → p5)) → False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656681171776716546744782369186 : ((((((False → (True ∧ (p3 ∨ p1))) → True) ∧ (((p1 → ((False → p2) ∧ p4)) ∧ p1) ∧ (p1 ∨ (p1 ∨ (p5 → p3))))) ∨ (p1 ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



