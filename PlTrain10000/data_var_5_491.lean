variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166006825749762187205390156778 : (((False ∨ p2) ∨ ((((((p4 ∧ p2) ∧ (p1 ∧ p2)) ∨ (p5 ∧ p2)) ∧ p5) ∧ p4) ∧ p3)) ∨ (((False → p1) ∨ ((p4 ∨ p1) ∧ p5)) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178162259128207232928634034896 : ((((p5 → True) ∧ (p5 ∧ (((True → False) → p5) ∨ (p1 → True)))) → p4) ∨ ((p1 → (p1 → (((True ∨ p5) ∧ p3) ∧ p1))) → (True ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147680217656557578671222691244 : ((((True → ((((p1 ∨ (p5 ∨ True)) ∧ (p2 → p4)) ∧ (True → p4)) ∧ False)) ∧ ((p1 ∨ p5) ∨ p2)) → False) ∨ (p5 ∨ (True ∧ (p4 ∨ p5)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h6 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h7 := h2 h6
      -- We need to get the right conjuct of h7 based on <expert-advice>.
      let h8 := h7.right
      -- False on the left can always be used.
      apply False.elim h8
    case inr h9 =>
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h10 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h11 := h2 h10
      -- We need to get the right conjuct of h11 based on <expert-advice>.
      let h12 := h11.right
      -- False on the left can always be used.
      apply False.elim h12
  case inr h13 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h14 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h15 := h2 h14
    -- We need to get the right conjuct of h15 based on <expert-advice>.
    let h16 := h15.right
    -- False on the left can always be used.
    apply False.elim h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225762270675732955161772975792 : (((p5 → True) ∧ p4) ∨ (((((p2 ∨ p1) → p2) ∨ (p4 → (p5 ∧ p1))) → ((p2 → False) ∧ False)) ∨ (True → (True ∨ ((p4 ∧ p2) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56571812036888432731781394520 : (((True → (p4 ∧ (True ∨ p3))) → ((((((p3 → p1) ∨ (True → False)) ∨ (p5 ∧ p1)) → p3) ∧ p1) ∨ ((False ∧ False) → (p3 ∧ True)))) ∨ p4) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158522221693418574053202835563 : (((p4 ∨ False) → (False ∨ (((p1 → (True ∧ (p4 ∧ p3))) → (p1 ∨ (False ∧ (p1 ∧ p4)))) ∨ True))) ∨ ((((p2 ∧ False) ∨ p2) ∨ p5) → False)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59099067041643271782428637145 : (((p5 ∧ p5) ∨ (((((True → (p4 ∨ p2)) → True) → p5) ∨ (True ∧ (((p3 ∧ p4) → True) ∨ p4))) ∨ (p2 ∧ (p3 ∧ (p4 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182063393308394991776273223802 : ((((p5 ∨ p5) ∨ ((p2 → (p4 → (p4 ∨ False))) ∨ p2)) ∨ p3) ∧ (((p4 → False) ∧ p2) ∨ ((((False ∨ (p3 ∨ False)) ∨ p4) → False) ∨ True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344799219259050890970747368428 : (p2 → (p4 → ((((p2 → p1) ∨ (p3 ∧ False)) → p5) → (((p1 ∨ p2) ∨ False) ∧ (((p3 ∨ p4) → p2) ∧ ((p2 → (p5 → False)) ∨ p2)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47339394734273499389762728869 : ((((p1 ∨ p2) ∧ ((((False ∨ False) ∧ (p3 → p4)) → p4) → (((((p1 → True) ∧ p5) ∧ (p5 ∧ p1)) ∧ p2) ∨ p3))) ∨ (True → True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_355942017257202739977050331614 : (p5 → ((True ∧ ((p5 → ((((p1 ∨ p3) ∧ ((p4 ∨ (((p4 → p1) ∨ p4) ∨ True)) ∨ p4)) ∨ p4) → p2)) ∨ p5)) → ((p2 → p1) ∨ p5))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_809067888135197976764165365273 : (((p5 → ((False ∨ (((p3 → p5) ∨ (((False ∧ p1) → (((True → False) → p5) ∨ p3)) ∨ p2)) → ((p1 ∨ p1) ∨ (p1 → p4)))) ∧ p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147236891033442634665462974011 : (((((p5 → (((False → True) ∧ ((False ∨ p3) ∧ (p2 → ((False → False) → True)))) → False)) → False) ∧ p1) ∨ p3) ∨ ((p2 ∧ (p4 ∨ True)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_715152920322287205445473713682 : ((((p5 ∨ (p4 ∨ ((False ∧ p5) → p5))) → ((False ∨ (True → True)) → (p3 ∨ ((p2 ∨ (p5 ∧ p2)) ∨ (((p4 ∧ p1) → p5) ∨ p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137226853532852018236606555488 : ((p1 ∧ (((((p4 ∧ (p3 → (p1 ∨ ((False ∧ p4) ∧ (True → True))))) → ((True → True) → False)) ∨ p2) → p1) → p1)) ∨ (False ∨ (p3 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351418317165909864151893371421 : (p4 → ((False ∧ (((p4 ∨ (False ∨ p1)) → ((((p1 ∨ p5) ∧ p2) ∨ (p3 ∨ (p3 ∨ p4))) ∨ p5)) ∨ p3)) ∨ ((p4 → (p2 ∧ False)) → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_764814255625147427737510975404 : (((p4 ∧ ((((((p3 ∧ p4) → True) ∨ ((p2 → ((True ∧ p2) ∧ ((True ∨ p5) → p1))) ∨ p1)) ∧ ((p3 ∨ p5) → False)) → p4) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120875587088022485549850968118 : ((((((p3 ∧ p2) ∨ (True → True)) → (False ∧ p3)) ∧ (p2 ∨ (((p3 ∨ (p5 ∧ (True → (p2 → True)))) ∨ p5) → p5))) ∨ p4) → (p4 ∨ p1)) := by
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
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h6 : ((p3 ∧ p2) ∨ (True → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h8 := h3 h6
      -- We need to get the left conjuct of h8 based on <expert-advice>.
      let h9 := h8.left
      -- False on the left can always be used.
      apply False.elim h9
    case inr h10 =>
      -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
      have h11 : ((p3 ∧ p2) ∨ (True → True)) := by
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h12
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h3, we can now drive its conclusion.
      let h13 := h3 h11
      -- We need to get the left conjuct of h13 based on <expert-advice>.
      let h14 := h13.left
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_120427843896401507286921849522 : (((p4 → (((p5 ∧ ((p2 ∨ (False ∨ (True ∨ ((True ∧ ((p1 ∨ (p3 ∧ False)) ∨ p4)) ∨ p3)))) → p5)) ∨ True) ∧ False)) ∧ p2) → (p4 → p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h5 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h6 := h3 h5
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- False on the left can always be used.
  apply False.elim h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136673818993476708433845703266 : (((p4 ∨ (p1 → p4)) → (((((False → p2) → (p5 ∧ (p1 → False))) → p5) → p2) ∧ ((p5 ∨ p2) ∧ (True ∧ p1)))) ∨ ((True ∨ p1) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233323360999673899670677835160 : ((True ∨ (False → p1)) → (p2 → ((p3 ∨ ((p4 ∨ p3) ∨ False)) → ((((((False → p4) → p2) → ((p3 ∨ p3) ∧ p2)) ∧ False) ∨ False) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
  case inr h7 =>
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h10 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h14 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h15 =>
      -- False on the left can always be used.
      apply False.elim h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_219059342044526168979765766561 : ((p5 ∧ (p3 ∧ (p3 ∨ True))) → (p5 ∧ ((((((p5 → ((p4 ∧ (p5 → (p2 → p3))) ∧ p2)) ∨ (True ∧ False)) ∧ p1) → True) → p1) ∨ p3))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h7 =>
    -- One of the premise coincides with the conclusion.
    exact h2
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h12
  case inr h13 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213820566662301837705015720023 : (((p4 ∧ (p5 ∧ p3)) ∨ p1) ∨ (p2 ∨ (p5 → (((p5 ∨ ((p5 ∨ p4) → (p4 ∧ ((p3 → (p2 ∨ False)) ∧ (p1 → p2))))) ∨ p5) ∧ p5)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40051723211823953963064080270 : ((((((p4 ∧ ((p2 ∧ (((p1 → p5) ∨ p3) ∧ (p4 ∧ (p4 → (p5 → p3))))) ∧ ((p5 ∨ p5) ∨ True))) ∨ False) ∨ True) ∧ p5) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149827256530819372224328248452 : ((p1 ∨ ((((True ∨ (p5 ∧ True)) → False) ∨ (((p2 ∧ (p4 → p3)) ∨ (p1 ∧ p4)) ∨ p1)) ∨ (p3 → p3))) ∨ (((p5 → p4) ∧ p1) ∨ False)) := by
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
theorem thm_5_vars_244686884422158623142168219685 : ((p1 ∧ True) ∨ (((p3 → True) → ((((p2 ∨ p2) → (p3 ∧ ((True → (True ∧ p2)) → (p2 ∧ p4)))) ∨ True) ∨ (p3 → p1))) ∨ (p5 ∧ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186654930291379805823227597420 : ((((p1 ∧ (p2 ∧ (p2 ∨ p5))) ∨ False) ∧ (p3 ∧ (True ∨ True))) → ((False ∨ ((((p2 ∧ False) → False) → True) ∧ ((p3 ∨ True) ∧ p4))) ∨ True)) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h3.left
      let h11 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h11
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
    case inr h14 =>
      -- Conjunctions on the left can always be decomposed.
      let h15 := h3.left
      let h16 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h16
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
    -- False on the left can always be used.
    apply False.elim h19



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_207282727794821165207133340207 : (((((False → True) → True) → False) ∨ p2) → (((p3 ∨ (p1 ∨ p4)) ∧ (p2 → False)) ∨ ((False → (True ∨ (True ∨ (p1 → (p2 ∨ p1))))) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : ((False → True) → True) := by
      -- Implications on the right can always be decomposed.
      intro h4
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h5 := h2 h3
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Implications on the right can always be decomposed.
    intro h7
    -- False on the left can always be used.
    apply False.elim h7
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_160956321958587904536853230175 : ((((p2 ∧ p5) → p5) ∧ ((False → ((p4 ∧ (p2 ∨ p2)) → p4)) → (p4 ∧ ((p5 ∧ p2) ∧ True)))) → (p4 → ((p5 → (p3 ∨ p3)) → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (False → ((p4 ∧ (p2 ∨ p2)) → p4)) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- Implications on the right can always be decomposed.
    intro h8
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h12 =>
      -- False on the left can always be used.
      apply False.elim h7
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h13 := h5 h6
  -- We need to get the right conjuct of h13 based on <expert-advice>.
  let h14 := h13.right
  -- We need to get the left conjuct of h14 based on <expert-advice>.
  let h15 := h14.left
  -- We need to get the right conjuct of h15 based on <expert-advice>.
  let h16 := h15.right
  -- One of the premise coincides with the conclusion.
  exact h16



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215821613520306916101439498022 : ((p2 ∨ ((p3 → p1) ∧ p5)) ∨ ((p4 → p2) → ((True ∨ p2) ∧ (((p3 → (p2 ∨ p4)) ∨ (False → ((p3 ∧ p2) → (p2 ∨ p3)))) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_242136694259562128897005555293 : ((p2 → True) ∧ ((((((p2 ∨ (p2 ∨ p3)) ∨ ((((True ∧ p4) ∧ p2) ∨ p4) ∨ p3)) ∨ (p2 → (p5 → p4))) ∧ p5) ∧ p1) → (False ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
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
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h8 =>
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
      case inr h10 =>
        -- Disjunctions on the left can always be decomposed.
        cases h10
        case inl h11 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
    case inr h13 =>
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h14 =>
        -- Disjunctions on the left can always be decomposed.
        cases h14
        case inl h15 =>
          -- Conjunctions on the left can always be decomposed.
          let h16 := h15.left
          let h17 := h15.right
          -- Conjunctions on the left can always be decomposed.
          let h18 := h16.left
          let h19 := h16.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
        case inr h20 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h6
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h6
  case inr h22 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157773327997453963395735321577 : ((((p5 ∧ (((True ∨ p4) ∨ p2) ∧ (p4 ∧ (p5 ∧ p3)))) ∧ False) ∨ (p5 → (p2 → (p1 ∨ p2)))) ∨ ((p4 ∨ p3) ∨ (p1 ∧ (p2 ∨ p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111037884465394536306953860319 : ((((p3 ∨ (((p3 ∨ p4) ∧ (p3 ∨ ((p5 → p2) ∧ p5))) ∧ (False ∨ (True ∧ False)))) ∧ (p4 ∨ ((False ∧ p2) → p5))) ∧ p1) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165584140763875717903015861351 : (((p5 ∧ ((p3 → p3) ∧ ((p2 ∧ p2) ∧ p3))) ∨ (((p1 ∨ p4) ∨ True) ∨ (p3 ∧ p5))) ∨ (True ∨ (((p2 → True) ∧ p1) ∧ (p2 → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_727452895868750069682923001141 : ((((p3 ∧ (p2 ∨ p4)) ∨ (p2 → ((p3 → ((p4 ∨ p4) ∨ (((p5 → False) ∧ p5) ∧ False))) ∨ (((p2 → p3) ∨ (True ∨ False)) → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_261466308756429209366566200764 : ((p5 → p2) → (((p5 ∨ False) ∨ p2) ∨ (p5 ∨ ((((((p2 → ((p2 → p3) ∧ True)) ∨ p5) ∨ (p4 ∧ p5)) ∨ (False ∧ p2)) ∨ p2) ∨ True)))) := by
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
theorem thm_5_vars_715116809798175913124613043175 : ((((p4 ∨ (p2 ∧ (p5 → (p5 ∧ False)))) → ((((p1 ∧ (((False ∨ (p1 → p3)) ∨ False) → p2)) ∧ p3) ∨ p5) ∨ (False → (p1 → p1)))) ∨ p3) ∧ True) := by
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
    -- False on the left can always be used.
    apply False.elim h3
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- Implications on the right can always be decomposed.
    intro h9
    -- False on the left can always be used.
    apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50480138790445518285578453120 : (((p2 → ((((p5 ∨ (p3 ∨ (p1 ∧ p5))) ∨ p1) ∨ p1) → (p4 → (p3 ∧ ((p5 ∧ p4) → p3))))) ∨ (((p2 ∧ False) ∧ p3) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206137263585819455839584112166 : ((p4 ∧ (p1 ∨ ((False ∧ p4) ∧ False))) ∨ ((((p2 ∨ True) → False) → (((True ∧ ((False ∧ (p5 ∨ p5)) → True)) → False) ∨ (True ∧ False))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586296025019663788025195537909 : (((((((p3 → (p2 → p4)) → (p5 → (p2 → p4))) ∨ (((((p3 ∧ p3) → p5) ∨ False) ∨ (True ∧ p1)) → (p4 → p3))) ∧ p1) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225130104670567713377713895906 : (((p3 ∧ True) ∧ p1) ∨ ((((p2 → ((p1 → True) ∨ p1)) ∨ p3) → (p3 ∨ True)) ∧ ((True → p5) → (p1 ∨ ((p1 ∨ (True ∨ p3)) ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_776523849274120957107346210998 : (((p1 ∨ (((p3 → (((p5 ∨ p5) ∧ (p2 ∨ p5)) ∧ p1)) ∧ (((True ∧ p2) ∨ False) ∨ ((p1 ∨ ((p5 ∧ False) ∧ True)) ∧ p5))) ∨ False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_797855614644966159320624150663 : (((p1 → (((((p3 → p3) ∨ (p2 ∧ ((p5 → (((p3 → p1) → (False ∧ p5)) ∧ p2)) ∨ (p1 ∨ p3)))) → p4) → False) ∨ (True ∨ p5))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134107742080386056948873114108 : ((((((p1 → (((p4 ∨ p2) ∧ p2) ∨ (p4 ∧ ((p2 → True) ∨ p3)))) → p5) ∨ (p4 → p2)) ∧ (p4 → p1)) ∨ True) ∨ ((p1 ∨ False) → p5)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135660122287429138095100290983 : ((((p5 → p2) ∨ (True → (p2 → (p4 → (((p1 ∧ p1) → (p3 → p4)) ∨ p5))))) → ((p2 ∧ p5) ∨ (True ∨ p1))) ∨ ((False ∨ p2) ∨ p4)) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_39375151380038519267767805190 : (((p3 ∧ (((True ∨ (p4 ∨ p2)) ∧ p2) ∨ (p3 ∨ (p5 ∨ (p1 ∧ ((p5 → (((p4 ∧ p1) ∨ (p2 ∨ p3)) ∨ p3)) ∧ p1)))))) ∧ True) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197016200931025116972324089705 : (((((p1 → p4) ∨ p4) ∨ (p4 → p5)) ∨ p4) ∨ ((p4 ∧ (p2 → (((p5 ∧ p5) ∨ (p5 ∨ (p5 ∧ p2))) → ((p3 ∨ p3) ∨ False)))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40257936874674344036666252350 : ((((p2 ∨ ((((((p2 ∧ False) ∨ (True ∨ ((True ∨ (p1 → (p1 → p1))) ∨ False))) → p5) → p1) ∧ True) ∨ (p2 ∧ True))) ∧ True) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595113049910357582691962058975 : (((((((True ∨ p2) ∨ (((p5 ∨ (p2 → (True ∧ False))) ∨ False) → True)) ∧ p1) → ((p4 ∨ (p4 ∨ (p4 ∨ p2))) → (p1 ∧ p5))) ∧ p5) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_313118927407171641590700739139 : (p3 ∨ (((True ∨ ((((p3 ∨ ((p1 → False) ∨ p3)) ∧ (p4 ∨ True)) ∨ ((p1 ∨ (p4 → p1)) ∧ p5)) → p1)) → (p1 ∨ (p2 ∨ p5))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_182742166280162804218446189241 : ((((p2 → True) ∧ (p5 ∨ p5)) ∨ ((False → (p5 → p1)) → True)) ∧ (p3 ∨ (p1 → (((p3 → ((p5 ∧ (True → p2)) ∧ p4)) ∧ p1) ∨ True)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257506678399916633477135304863 : ((p3 ∨ False) → ((p4 ∧ (((p5 ∧ (p5 → False)) → (False ∧ False)) ∧ (False ∨ (p3 → (False ∨ (p1 ∨ True)))))) ∨ ((False ∧ (p1 ∧ p5)) → p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h4
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137855994102409893536793319473 : ((p3 ∨ (True ∧ ((p2 → ((((False → (p2 ∨ p3)) → ((True → p1) ∧ True)) ∨ p5) ∨ (p4 ∧ p1))) ∧ (p2 → p5)))) ∨ (p2 ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57956296343063515403978223911 : (((p2 → (True ∧ p1)) → ((((p5 ∨ (p4 → (False ∧ p1))) ∨ p5) → p1) ∨ (True ∨ ((p4 → (True ∧ ((p2 ∨ True) → p1))) ∨ p5)))) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300367059879005452809148781110 : (False ∨ ((((p1 → (p5 ∨ (True ∨ (((p4 ∨ p4) ∧ p4) → p5)))) ∧ ((p1 → p2) ∧ (p3 → (p2 → p4)))) → p4) ∨ ((p1 ∧ p1) → p1))) := by
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
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172378970148580968142380823536 : (((((False ∧ (False ∧ p2)) → p1) ∧ p1) → ((((p2 ∨ p4) ∨ p3) → False) ∧ p3)) ∨ (p2 → (((p4 ∧ p4) → False) → (p1 ∨ (True → p2))))) := by
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
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134800351834525074288726238104 : (((p4 ∧ (((p2 ∨ (((p4 ∧ p5) → ((p5 → False) ∧ (False ∨ (False ∧ p1)))) ∧ p2)) ∧ (p4 → False)) → False)) → False) ∨ (True ∨ (p5 ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166152105337186210718161265474 : ((False ∧ ((p4 ∨ (p3 ∧ ((((p2 ∨ True) ∧ (p2 ∨ (p2 ∧ p1))) ∧ False) ∧ p1))) ∨ p1)) ∨ ((p5 ∧ ((False ∧ p4) ∨ p1)) → (p2 ∨ p5))) := by
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
    -- False on the left can always be used.
    apply False.elim h5
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178104549895250388346527858324 : (((((p4 → (((p2 → p1) ∨ p1) ∨ p3)) ∧ True) ∨ (p4 ∧ p2)) → p4) ∨ ((True ∧ p2) → (p4 ∨ (((True ∧ (p4 ∨ False)) ∨ True) ∨ False)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116433447974268791954663136532 : (((p1 → (True ∧ p1)) → (((p2 → False) ∨ (((p5 ∨ (p4 ∧ (p2 ∨ (True ∧ p2)))) ∨ (p3 ∨ True)) ∨ p5)) ∨ (p3 ∧ False))) ∨ (True ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48502986443546951673582449448 : (((((((p2 → False) ∧ (True ∧ p3)) ∧ (p4 → (False ∧ ((p5 ∧ ((p4 → p2) ∧ p4)) ∨ p4)))) ∨ p1) ∨ p2) ∧ (False ∧ (True → p5))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305184245611734578675513678910 : (p1 ∨ (((p1 → p1) ∧ ((False ∨ (p4 ∧ (((p3 → p2) → (True ∧ (p3 → (p2 → p5)))) ∧ p4))) ∧ p1)) ∨ ((p5 ∧ False) → (False → p4)))) := by
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
theorem thm_5_vars_345370861005477702671756502451 : (p3 → (((((((True → (p5 ∨ False)) ∧ True) ∨ (p5 ∨ p3)) → p5) → (((p4 ∨ ((p5 ∨ (p3 → p2)) ∧ p3)) ∨ p5) ∧ p2)) ∨ True) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_75672729790500942904540375965 : (((((((((p3 ∨ p3) ∨ (p5 → True)) ∧ True) → (p4 ∨ p4)) → (p2 ∨ ((p2 ∨ ((p3 → p1) ∧ p2)) ∨ p1))) ∨ True) ∨ False) → p2) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((((p3 ∨ p3) ∨ (p5 → True)) ∧ True) → (p4 ∨ p4)) → (p2 ∨ ((p2 ∨ ((p3 → p1) ∧ p2)) ∨ p1))) ∨ True) ∨ False) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166584310253724301238631615421 : ((True → (((p1 ∧ p3) ∧ ((True → False) ∨ p4)) ∨ ((p5 → (False ∨ p1)) ∨ (False → False)))) ∨ ((p2 ∧ ((p3 → True) → p1)) ∧ (False ∨ p3))) := by
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
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134700478011064341785419762824 : (((((False ∨ p4) ∧ (p5 ∧ p5)) ∨ ((p4 ∨ p3) → (((False ∧ (p5 ∧ True)) ∧ p3) ∨ ((p1 → p5) ∨ p3)))) → p1) ∨ (True ∧ (False → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165329799188140760332684817453 : ((((p2 ∧ ((p1 → ((p1 ∧ p3) ∧ False)) ∧ (p5 ∨ p2))) ∨ p2) ∧ ((p5 → True) ∨ p2)) ∨ (((True ∨ p3) ∨ p2) ∨ (True ∧ (True ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_707004561077002667726896762918 : (((((p3 ∧ ((p3 ∧ p1) ∨ (p1 ∧ p5))) ∨ p1) ∨ (p3 ∨ (True → ((((p4 → p2) → (p2 ∨ True)) → p5) ∨ ((True ∧ True) ∧ True))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51603108531928486570585821217 : (((p4 → (False ∧ (((p3 ∨ p2) ∨ (((False ∧ (True → (p4 ∨ p4))) ∨ p2) ∨ p2)) → p2))) → (p1 ∧ (((p3 ∨ True) ∨ p1) → p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60671161820324952039134181458 : ((True ∧ ((((p4 ∨ ((((True ∨ p2) ∨ p3) ∧ p5) → ((False ∨ p1) ∨ p4))) ∨ p3) → p1) → (p3 → (p2 ∨ ((p2 → p1) ∧ p3))))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h4 : ((p4 ∨ ((((True ∨ p2) ∨ p3) ∧ p5) → ((False ∨ p1) ∨ p4))) ∨ p3) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h4
  -- One of the premise coincides with the conclusion.
  exact h5
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206431687346718964477908187461 : ((p4 ∨ ((p1 ∧ (p1 ∧ p5)) ∧ p4)) ∨ (((p3 ∧ p1) ∧ ((((p4 → False) → False) ∧ (p5 ∧ p2)) ∧ ((True ∧ p3) ∨ (p3 ∨ False)))) → p1)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h9.left
  let h11 := h9.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h12 =>
    -- Conjunctions on the left can always be decomposed.
    let h13 := h12.left
    let h14 := h12.right
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h15 =>
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- One of the premise coincides with the conclusion.
      exact h5
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_741099058400542808402709682962 : ((((p4 ∨ False) ∨ (((p2 → (p1 ∨ p1)) ∨ (p3 ∨ ((p3 ∨ p1) → (((False → ((p5 ∨ p3) ∨ p2)) → (p2 → False)) → p3)))) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_1499473230057352285898349544 : ((((p1 → (((((True ∧ p5) ∧ p5) → p4) ∧ p3) ∨ (p3 → ((p1 → p3) ∧ p5)))) ∨ False) ∨ ((p1 ∧ p3) ∨ True)) ∨ (False → True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_623718813839199514608593332247 : ((((p1 ∨ (((((p3 ∨ p1) ∧ (p1 → (p4 ∨ (p5 ∨ (p4 ∧ p5))))) ∨ ((True → p2) ∨ False)) → (p3 → p1)) ∧ (False → True))) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_805920139723019833536708717565 : (((p4 → (((((p4 ∨ (((p2 ∨ p2) ∨ (False ∧ p4)) → (True → p3))) ∧ (p1 ∨ (p3 ∨ (p4 → (p2 ∧ p4))))) → p5) → p1) ∧ p1)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_263383472557374858735876582494 : (True ∧ (((((False → False) → p4) ∧ ((((p3 ∨ (p5 → True)) → p1) → (p2 → ((p1 ∨ p5) ∧ p4))) → p3)) → p5) ∨ ((p1 ∨ False) → True))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117502167790168984812417035117 : ((p2 ∧ ((((p2 → (p2 → p4)) → (((p3 → p2) ∧ p4) ∨ ((p2 ∧ p1) ∨ False))) ∧ (p2 ∨ (p3 → (p2 ∨ p2)))) ∧ p5)) ∨ (True ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338375559746094128663188744988 : (p1 → ((p5 ∧ ((False ∧ p4) ∨ p3)) ∨ (((p5 ∧ p5) ∨ (False → (False ∧ (False ∨ (p4 → (False ∧ False)))))) ∨ ((p3 ∧ True) ∨ (False ∧ p5))))) := by
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
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_85978727286615229727828495582 : ((((((False ∨ (p3 ∨ p4)) ∨ True) → True) → (True ∧ p1)) ∧ (p2 → (p4 ∨ (p2 ∧ ((p2 → (p4 → False)) ∧ ((p2 ∧ p5) → p4)))))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((False ∨ (p3 ∨ p4)) ∨ True) → True) := by
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h6 := h2 h4
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50371453709824269799573649570 : (((((True → p1) ∨ p5) → ((p4 ∨ (p2 ∧ (p4 ∧ (False → (p2 ∨ ((p5 ∧ p4) → False)))))) ∨ True)) ∨ ((False → (p4 ∧ True)) ∧ p3)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_147585498939087898082172658214 : ((((p4 → (((True ∨ True) ∨ True) → ((p2 → ((True ∧ p5) ∨ p3)) ∧ (p3 ∨ (p3 ∧ p3))))) ∧ p5) → p4) ∨ (p4 ∨ (False → (p4 → p5)))) := by
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
theorem thm_5_vars_311248578364834317003950618901 : (p2 ∨ ((p5 → p4) → (((((p2 → (((p2 → p4) ∨ p2) ∧ True)) ∨ p1) ∨ (p1 ∧ p2)) → p2) ∨ (p3 ∨ (True → (p5 ∨ (False → p1))))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778971320354685383465360293844 : (((p1 ∨ (p3 → ((((p4 → False) → (p2 ∧ (((p3 ∨ p3) ∧ (False ∧ (p3 → p4))) → (p5 → (False ∧ p3))))) ∧ (True → True)) → p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_926413715208014585279582442329 : (((((((p4 ∧ p5) ∨ (True ∨ p1)) ∨ p4) ∨ ((p2 ∨ p2) ∨ True)) → (((((p2 ∨ (False ∨ p4)) ∨ (True ∨ p3)) ∨ p1) → p4) ∧ False)) → p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p4 ∧ p5) ∨ (True ∨ p1)) ∨ p4) ∨ ((p2 ∨ p2) ∨ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61611488391340416056810481997 : ((p1 ∧ ((p5 ∨ p5) ∧ ((p5 ∨ p5) → ((p5 → (True → (((p1 ∨ (False → (p5 ∨ (p2 ∨ p3)))) ∧ p1) ∨ p1))) ∧ (p1 ∨ p5))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27393850566130525748548894344 : (((p1 ∧ p3) → (((((((p5 ∨ p5) → ((((p4 ∧ (p5 ∨ (False → p4))) → False) ∧ True) ∧ False)) ∨ p2) ∨ p1) ∧ p3) ∨ p4) ∨ p1)) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56432040258169479218343567294 : ((((p1 → True) ∧ (p5 → p5)) → (((p4 → (p3 ∨ (p2 ∧ p4))) ∧ False) ∨ ((((p5 ∨ True) → (p4 ∨ True)) ∨ (True ∨ False)) ∧ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61424734721568405575016316499 : ((p1 ∧ (((True ∨ ((False ∧ p4) ∨ (p3 ∧ (((((False → p3) → (False ∨ p5)) ∧ p1) ∨ True) ∧ True)))) → ((p1 → True) ∨ p5)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200303105574882763413400520397 : (((p2 ∧ True) ∧ (p4 → ((p5 ∨ p2) ∧ True))) → (((True ∧ (p3 → False)) ∨ (p5 → (p2 ∧ True))) → (((p2 → False) ∧ (p2 ∧ p5)) → p1))) := by
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
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- Conjunctions on the left can always be decomposed.
    let h9 := h8.left
    let h10 := h8.right
    -- Conjunctions on the left can always be decomposed.
    let h11 := h1.left
    let h12 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h15 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h13
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h16 := h4 h15
    -- False on the left can always be used.
    apply False.elim h16
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h1.left
    let h19 := h1.right
    -- Conjunctions on the left can always be decomposed.
    let h20 := h18.left
    let h21 := h18.right
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h22 : p2 := by
      -- One of the premise coincides with the conclusion.
      exact h20
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h23 := h4 h22
    -- False on the left can always be used.
    apply False.elim h23



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53002553076419282679458713864 : (((((((p4 ∧ p3) ∧ p2) ∨ False) ∧ p4) ∧ (p3 → (p5 ∧ p3))) ∧ (False ∨ (True ∧ (((p5 ∨ (p5 → True)) → (p4 ∨ True)) ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38507525566902575494325886151 : ((((p2 ∧ (p4 ∨ ((p4 ∧ True) ∧ (((p3 ∧ p5) ∧ p5) ∧ p1)))) ∨ ((True ∨ False) ∨ (True ∨ (p5 ∨ (False ∨ (p3 → True)))))) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_380245687157022457322005522530 : ((((((((p4 → (p1 ∧ ((p1 → (True ∨ True)) → False))) ∨ (True → (p2 ∨ (p5 → p1)))) → (p2 ∨ p1)) → (p5 ∧ False)) ∧ False) ∨ True) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_656247384764270928778414842276 : ((((((((((False → (p2 → p2)) ∨ p2) ∧ p3) ∧ p4) ∨ p2) ∧ p4) ∧ ((p1 ∨ (((False ∨ p3) → True) ∨ True)) → p2)) ∨ (False → p3)) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53370054649119673322568443179 : ((((p3 → ((p2 ∨ ((p2 → (p1 ∧ p2)) → p3)) ∧ p4)) ∨ p3) → (((p5 → ((p5 ∧ False) → p5)) → p3) → ((p3 ∧ p3) ∧ p3))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h4 : (p5 → ((p5 ∧ False) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- False on the left can always be used.
      apply False.elim h8
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h4
    -- One of the premise coincides with the conclusion.
    exact h9
  case inr h10 =>
    -- One of the premise coincides with the conclusion.
    exact h10
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h11 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h12 : (p5 → ((p5 ∧ False) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h13
      -- Implications on the right can always be decomposed.
      intro h14
      -- Conjunctions on the left can always be decomposed.
      let h15 := h14.left
      let h16 := h14.right
      -- False on the left can always be used.
      apply False.elim h16
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h17 := h2 h12
    -- One of the premise coincides with the conclusion.
    exact h17
  case inr h18 =>
    -- One of the premise coincides with the conclusion.
    exact h18
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h19 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h20 : (p5 → ((p5 ∧ False) → p5)) := by
      -- Implications on the right can always be decomposed.
      intro h21
      -- Implications on the right can always be decomposed.
      intro h22
      -- Conjunctions on the left can always be decomposed.
      let h23 := h22.left
      let h24 := h22.right
      -- False on the left can always be used.
      apply False.elim h24
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h25 := h2 h20
    -- One of the premise coincides with the conclusion.
    exact h25
  case inr h26 =>
    -- One of the premise coincides with the conclusion.
    exact h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324735764049698003766876881903 : (p5 ∨ ((p1 ∧ (p4 ∨ p5)) → (((p1 → (((True ∧ p5) ∧ p1) → (p5 ∨ True))) ∧ (p2 ∨ p3)) ∨ (p3 ∨ (((p1 ∨ True) ∨ True) ∨ False))))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22137798980475888963511525456 : ((((p1 ∨ (p3 → p1)) ∧ (p2 → (p1 ∨ True))) ∨ (p4 ∨ ((((p2 ∨ p2) ∧ True) → ((p2 → (p3 ∧ True)) ∨ p2)) ∨ (p3 ∨ p3)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h5
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157680277642941923109128715757 : (((False ∧ (((p2 ∨ (p3 → False)) ∨ p2) ∨ ((p5 ∨ p5) ∨ (False → p2)))) ∨ ((p2 → p3) ∧ p2)) ∨ ((False ∧ p5) → ((p4 ∧ False) ∧ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- False on the left can always be used.
  apply False.elim h2
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- False on the left can always be used.
  apply False.elim h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_45469127671739050826757855253 : (((False ∨ (((p2 ∨ (True → (((p1 ∨ p4) ∨ (p3 ∨ p4)) ∧ (((p4 ∧ p4) → ((p5 ∧ True) → p5)) ∧ p3)))) ∧ True) → p1)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40118308460874778699658500211 : ((((((p1 → p2) ∨ (((((p1 → (p1 ∨ p2)) → p2) ∧ ((p1 ∧ p5) ∧ p4)) ∧ True) ∧ (p1 ∨ True))) → (p4 ∨ False)) ∧ True) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_32428664536944301368701543417 : ((p2 ∨ (((((p1 → ((p4 ∨ p5) → (p1 → p2))) ∨ p1) ∨ p1) ∨ (False → (((p3 → (p5 ∨ (False ∧ True))) ∨ p5) ∨ p5))) ∨ True)) ∧ True) := by
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



