variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_305813713489576923758109257376 : (p1 ∨ ((p4 ∧ ((p3 ∨ (True ∧ (p3 → p3))) ∨ p2)) → ((p5 → (((False ∨ p5) ∨ False) ∧ (((p1 ∨ p4) ∧ (p1 → p4)) ∨ p4))) ∨ p2))) := by
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
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h6
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h10
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h10
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_685622147070263520168732298457 : (((((((((p2 ∧ p5) → (p4 → p5)) ∨ p5) ∨ (p1 → (p2 → p2))) ∨ (p5 ∧ p4)) ∨ p5) → (p1 ∨ (True ∨ (p3 ∧ (p4 ∨ False))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53279491442733998229415082854 : (((p3 ∧ (((p1 → p3) ∨ p5) ∧ (False ∨ ((p5 ∨ p4) → p1)))) ∨ ((p1 ∧ (True → p3)) ∧ (((p2 ∨ p1) → p1) → (p2 ∧ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_348044133241111052868969329875 : (p3 → ((False ∨ False) ∨ ((((((((True → p5) → p4) ∨ ((p3 → p4) → p1)) ∨ p2) ∧ p4) → (p1 → p3)) ∧ p1) → (p2 → (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314784841161098397090162408762 : (p3 ∨ ((p1 ∧ (((((True ∨ True) ∨ True) ∧ p3) ∨ p1) → (p1 → (p3 ∧ p3)))) → (p3 ∨ (((p1 → p4) ∨ ((p2 ∨ p1) → p3)) → p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : ((((True ∨ True) ∨ True) ∧ p3) ∨ p1) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h2
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h7 := h5 h6
  -- We need to get the left conjuct of h7 based on <expert-advice>.
  let h8 := h7.left
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56311249195891012119167417858 : ((((p3 ∧ (p1 → p4)) ∧ p3) → (((p4 ∨ p2) ∧ (((p3 ∧ (p1 ∧ False)) → p3) ∧ (p2 ∨ p5))) ∧ (True ∨ ((p4 → p4) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_215600437396481451250198466794 : ((p5 ∧ (p4 ∨ (p5 ∨ p5))) ∨ ((p3 ∨ p1) → ((True → (False ∧ ((p5 ∧ p1) → (p3 → (False ∨ p5))))) → ((p5 → p1) ∨ (p4 → p1))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h8 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h9 := h2 h8
    -- We need to get the left conjuct of h9 based on <expert-advice>.
    let h10 := h9.left
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148340578859573210922773100888 : ((((((p4 ∨ p5) ∨ p1) ∧ ((p3 ∧ p1) ∨ True)) ∧ (True ∨ (p4 ∧ p3))) ∧ (p5 ∧ (p1 ∧ (False → p2)))) ∨ (False ∨ (p3 → (True → True)))) := by
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
theorem thm_5_vars_257515201296577365981284183281 : ((p3 ∨ False) → ((p5 ∧ (p4 ∨ ((p3 → False) ∧ p5))) ∨ (((p2 → (p1 ∧ ((False ∨ ((p1 ∧ p2) ∧ False)) ∧ (False ∧ False)))) ∨ p5) ∨ p3))) := by
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
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165169908737002846687489200022 : (((True ∧ (p4 → (p2 ∧ (p1 → (True ∧ (p3 → ((False ∨ p5) ∧ p5))))))) ∧ (True ∧ p5)) ∨ (True → ((p3 ∨ (p2 ∧ True)) ∨ (p4 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40037810021056542029295604820 : (((((((p1 ∨ True) → True) → ((((p2 ∨ ((p5 ∧ p3) ∧ False)) ∧ (p5 ∨ True)) ∨ ((p5 → p2) → p2)) → p3)) ∧ p3) ∧ p1) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253942355573006843179109042442 : ((p1 ∧ p4) → (True ∧ ((p2 → (((p3 ∨ (((p3 ∧ p3) ∨ p2) ∧ (p5 ∧ (p4 → (p4 ∨ (p5 ∨ False)))))) ∧ p2) ∧ True)) ∨ (p1 ∨ p1)))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248302652255375684504482625046 : ((p2 ∨ p2) ∨ (p2 ∨ ((p1 ∧ (((False ∧ p3) → p3) ∧ (p3 ∧ ((p3 ∨ p4) ∨ p1)))) → (p2 ∨ (((p2 ∧ p2) ∧ (p2 ∧ True)) ∨ p1))))) := by
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
  let h4 := h3.left
  let h5 := h3.right
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Disjunctions on the left can always be decomposed.
  cases h7
  case inl h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h10 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
  case inr h11 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_948601871265585980154801993526 : ((((p2 → ((False ∨ p2) ∧ p2)) → ((True ∧ True) ∧ ((False ∨ p1) ∨ (((p4 → True) ∧ True) → ((((False ∨ False) ∧ p3) ∧ True) ∧ True))))) → p1) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (p2 → ((False ∨ p2) ∧ p2)) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h3
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- False on the left can always be used.
      apply False.elim h7
    case inr h8 =>
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h9 =>
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((p4 → True) ∧ True) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Implications on the right can always be decomposed.
      intro h11
      -- True on the right can always be proven directly.
      apply True.intro
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h12 := h9 h10
    -- We need to get the left conjuct of h12 based on <expert-advice>.
    let h13 := h12.left
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- We need to get the left conjuct of h14 based on <expert-advice>.
    let h15 := h14.left
    -- Disjunctions on the left can always be decomposed.
    cases h15
    case inl h16 =>
      -- False on the left can always be used.
      apply False.elim h16
    case inr h17 =>
      -- False on the left can always be used.
      apply False.elim h17
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142405510393047755679079249520 : ((p4 ∧ ((((p1 ∨ p4) → ((p4 ∧ p5) ∧ False)) → p1) → ((((p5 ∨ ((p1 → p2) → p4)) → p2) ∧ p1) ∧ p3))) → (p4 ∧ (p3 ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h4 := h1.left
  let h5 := h1.right
  -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
  have h6 : (((p1 ∨ p4) → ((p4 ∧ p5) ∧ False)) → p1) := by
    -- Implications on the right can always be decomposed.
    intro h7
    -- We want to use the implication h7 based on <expert-advice>. So we show its premise.
    have h8 : (p1 ∨ p4) := by
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h7, we can now drive its conclusion.
    let h9 := h7 h8
    -- We need to get the right conjuct of h9 based on <expert-advice>.
    let h10 := h9.right
    -- False on the left can always be used.
    apply False.elim h10
  -- We have shown the premise of h5, we can now drive its conclusion.
  let h11 := h5 h6
  -- We need to get the right conjuct of h11 based on <expert-advice>.
  let h12 := h11.right
  -- One of the premise coincides with the conclusion.
  exact h12
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233080136269935820405888016197 : ((p4 ∧ (True → False)) → ((p2 ∨ (((p5 ∧ p4) ∨ False) ∧ (p1 → ((((p3 → (p2 ∧ (True ∧ p5))) ∨ (p2 ∨ True)) ∨ p5) ∧ p3)))) ∨ p3)) := by
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
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184580903496352366636243967855 : (((p3 ∧ ((p4 ∧ (p1 ∨ p2)) → (True ∨ p1))) → (p1 ∧ p5)) ∨ (((((p4 ∧ False) → p4) → ((p3 ∨ p2) → (p5 ∨ p3))) → True) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_433019262958249776130296526797 : ((((((((p3 → ((p3 ∨ p3) ∨ True)) → p5) ∨ (p1 ∧ (p3 ∨ ((p2 → p2) ∨ p1)))) ∧ (p1 ∨ (p2 ∧ p2))) ∧ p1) → (p4 ∨ p1)) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
    cases h5
    case inl h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
    case inr h8 =>
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h3
  case inr h11 =>
    -- Conjunctions on the left can always be decomposed.
    let h12 := h11.left
    let h13 := h11.right
    -- Disjunctions on the left can always be decomposed.
    cases h13
    case inl h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
      case inr h16 =>
        -- Conjunctions on the left can always be decomposed.
        let h17 := h16.left
        let h18 := h16.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h3
    case inr h19 =>
      -- Disjunctions on the left can always be decomposed.
      cases h19
      case inl h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h22 =>
          -- Conjunctions on the left can always be decomposed.
          let h23 := h22.left
          let h24 := h22.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
      case inr h25 =>
        -- Disjunctions on the left can always be decomposed.
        cases h5
        case inl h26 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
        case inr h27 =>
          -- Conjunctions on the left can always be decomposed.
          let h28 := h27.left
          let h29 := h27.right
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h3
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185130015162907827858342914077 : (((p2 ∧ p2) → (p3 ∨ (False ∧ ((True → (p4 ∨ True)) ∧ p4)))) ∨ ((p1 ∨ p1) ∨ (p2 → ((p4 ∧ (p5 → p2)) → ((p1 → p1) → p2))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h2.left
  let h5 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255153685458083254623943123061 : ((p4 ∧ p3) → ((p1 ∧ True) ∨ ((((p4 ∧ (p3 ∧ p5)) ∨ ((p1 ∨ (p5 → p1)) ∨ (((p1 ∧ p3) → p5) → False))) ∨ (p2 → True)) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_646554475310055828387511449425 : ((((p1 → (((p4 ∧ p1) ∧ (p1 ∨ p2)) ∧ (((((p3 ∨ p3) ∨ (p3 ∨ True)) → ((True ∨ True) ∨ False)) ∧ p2) ∧ (p5 ∨ p2)))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205095799875957064423414770999 : ((((p4 ∨ p3) ∧ p1) ∧ (False ∨ p4)) ∨ ((p4 → (((p5 ∨ p4) → p2) ∨ p4)) ∧ (((p5 ∧ (p2 ∨ (False → True))) → p5) → (p2 → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622047550216954794557041930576 : ((((p2 ∧ (((((p1 ∨ p5) ∧ (p4 ∨ (False ∨ ((p5 → ((True ∧ False) → p4)) ∧ p1)))) ∨ p4) → ((p3 → p4) ∧ p5)) → p2)) ∨ True) ∨ p3) ∧ True) := by
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
theorem thm_5_vars_172628288738655563752915412107 : (((p3 ∧ False) ∧ (p2 → ((p2 ∧ (((p5 → p2) → False) ∨ (True ∨ p5))) ∧ True))) ∨ (p2 → ((p4 ∨ (p3 ∨ (p3 ∨ p2))) ∧ (p4 ∨ True)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158443914875572871703819547786 : (((p3 ∨ p2) ∨ (p1 ∨ (((((p1 ∧ ((True ∨ (True → p1)) ∨ p4)) ∨ p1) ∧ p5) ∧ p1) ∧ p1))) ∨ ((p4 → False) ∨ (False → (p3 ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_180938571085215429590552170157 : (((True ∨ False) ∧ (True → ((True ∧ (p3 → (p1 ∨ p1))) ∧ (False ∧ p4)))) → ((p5 → ((p2 ∨ p3) ∨ p3)) → (p3 ∨ (p5 → (True ∧ False))))) := by
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
    -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
    have h6 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h4, we can now drive its conclusion.
    let h7 := h4 h6
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We need to get the left conjuct of h8 based on <expert-advice>.
    let h9 := h8.left
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- False on the left can always be used.
    apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_251218532324458289192332069192 : ((p2 → p1) ∨ (p3 ∨ (((p4 → True) → (p3 ∨ (p4 ∧ p4))) ∨ ((False → p4) ∨ (p2 → ((True ∧ p5) ∧ ((p2 ∨ p5) ∨ (p1 ∨ True)))))))) := by
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135319804443342320976895671143 : (((((p5 ∨ (False ∧ True)) ∧ (((p1 ∨ p5) → (p1 ∧ p2)) ∨ p4)) ∧ ((p4 ∧ p4) ∧ p2)) ∧ ((p5 ∨ p1) ∧ False)) ∨ ((p3 ∧ p4) → p3)) := by
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
theorem thm_5_vars_215087932891437422409263532428 : (((False → p1) → (p2 ∧ False)) ∨ (p2 → ((True ∨ (((((((True ∧ p5) ∨ p4) ∧ p3) → (False ∨ (p5 → p2))) ∧ p3) ∧ p1) ∧ p1)) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44700306712804204827097269224 : ((((((p5 ∨ True) ∨ True) → p5) ∧ ((((False ∧ (True ∨ (p2 → p4))) ∨ p2) ∧ ((True ∧ (p1 ∧ p2)) ∨ (p3 → p5))) → p1)) → p5) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : ((p5 ∨ True) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_179577948370828382792579557185 : ((p2 → (p4 ∧ ((p2 ∧ (False ∧ p4)) ∧ ((p5 ∧ False) → (True ∧ p5))))) ∨ ((False ∨ ((p4 ∧ (p1 → p4)) → (p4 → p3))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147747132495855359329641616082 : (((((False → p2) ∨ p3) ∧ ((((p2 → p4) → p4) ∨ p1) ∧ (p4 ∧ (False → (True ∧ (p4 ∨ p5)))))) → False) ∨ (True ∧ ((p1 ∨ False) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165468336107230622053213256750 : (((p1 ∨ ((p2 ∧ (((p5 ∨ False) ∧ True) ∨ p2)) → p5)) ∧ ((p4 ∨ p5) ∨ (False ∧ True))) ∨ (p2 → (p1 → (((True ∧ p4) → p1) ∧ True)))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_200344050987979064430131256590 : (((p4 ∨ p1) ∧ ((True → (p2 ∧ False)) → p2)) → ((p2 ∨ (((p4 → False) ∨ (p5 → (p2 ∨ p2))) ∨ p1)) ∨ ((p4 → False) → (p1 ∧ p4)))) := by
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
    -- Implications on the right can always be decomposed.
    intro h5
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h7 := h5 h6
    -- False on the left can always be used.
    apply False.elim h7
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h8 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165509961587968577164515624928 : (((((p4 → p4) ∨ ((p1 ∧ (p3 ∧ p4)) → p5)) ∨ True) → (False ∨ (p4 → (p2 ∨ p4)))) ∨ ((True ∧ p2) ∨ (False → ((p3 → p2) → p2)))) := by
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
theorem thm_5_vars_118101643302885550968657164037 : ((False ∨ (((((p3 ∨ (p2 ∧ (p4 → False))) ∧ p5) ∨ ((p2 ∨ True) ∨ ((False ∨ (p1 ∧ (p2 ∨ True))) ∨ p5))) → p3) ∨ True)) ∨ (p1 ∧ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64590570500531761938663918192 : ((p1 ∨ ((p5 → p1) ∧ ((p3 → (((((p2 → p3) → p5) ∧ True) → ((((False ∧ False) ∨ (True → True)) ∧ p1) → True)) → p5)) ∧ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704239489205318199437330829516 : ((((((True → True) ∧ ((p3 ∧ p5) ∧ p5)) → (p1 ∧ p2)) → (p1 ∨ (p2 ∨ ((p4 ∨ ((p4 → (p3 → (p4 ∨ p5))) ∨ p5)) ∨ p4)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613352897936563617300962759517 : ((((((p3 → p4) ∨ (p4 → ((True ∧ p3) ∧ (((p4 ∧ True) ∧ (p5 ∧ p4)) ∧ (p3 → (True ∨ (p5 ∨ p4))))))) → (p4 → p3)) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_148367483330970008690366459825 : ((((p4 ∧ (p5 ∧ ((p3 ∨ p1) ∨ (p3 ∨ (p5 ∧ (p5 → p5)))))) ∧ False) ∨ ((p2 ∨ p5) ∨ (True ∨ False))) ∨ ((p4 ∧ p1) → (p2 ∨ True))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_195668851776244334599844887721 : (((p5 → True) ∧ (((False ∧ p5) ∧ False) → p2)) ∧ (((p5 ∨ ((((p2 → (p5 ∧ True)) ∧ p1) ∧ p4) ∧ (p4 ∨ p4))) ∧ (p1 → True)) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699507222634786881603042595904 : ((((((p1 → p1) ∨ ((p2 ∨ p2) ∨ (p3 ∧ (p2 → p5)))) ∨ p3) → (((True ∧ p5) ∨ p5) ∨ (p5 → (p3 ∨ ((p1 ∧ p3) → p3))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216983997187027718868892889035 : (((p4 → (True ∨ False)) ∧ p3) → ((((p2 ∨ p1) → p1) ∧ (((p2 ∧ (p4 ∧ (p1 ∨ p1))) → False) ∨ ((p4 ∧ p5) → (p1 ∧ p3)))) ∨ True)) := by
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
theorem thm_5_vars_52138931301631341052706214861 : ((((((p1 ∨ (p2 ∨ False)) ∧ p4) ∨ ((p2 ∨ (p3 → p5)) ∨ False)) ∨ (True → p3)) → ((False ∧ False) ∨ (((p1 ∧ p4) ∧ True) → p4))) ∨ p4) := by
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
      -- Conjunctions on the left can always be decomposed.
      let h4 := h3.left
      let h5 := h3.right
      -- Disjunctions on the left can always be decomposed.
      cases h4
      case inl h6 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h7
        -- Conjunctions on the left can always be decomposed.
        let h8 := h7.left
        let h9 := h7.right
        -- Conjunctions on the left can always be decomposed.
        let h10 := h8.left
        let h11 := h8.right
        -- One of the premise coincides with the conclusion.
        exact h11
      case inr h12 =>
        -- Disjunctions on the left can always be decomposed.
        cases h12
        case inl h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h14
          -- Conjunctions on the left can always be decomposed.
          let h15 := h14.left
          let h16 := h14.right
          -- Conjunctions on the left can always be decomposed.
          let h17 := h15.left
          let h18 := h15.right
          -- One of the premise coincides with the conclusion.
          exact h18
        case inr h19 =>
          -- False on the left can always be used.
          apply False.elim h19
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h20
      case inl h21 =>
        -- Disjunctions on the left can always be decomposed.
        cases h21
        case inl h22 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h23
          -- Conjunctions on the left can always be decomposed.
          let h24 := h23.left
          let h25 := h23.right
          -- Conjunctions on the left can always be decomposed.
          let h26 := h24.left
          let h27 := h24.right
          -- One of the premise coincides with the conclusion.
          exact h27
        case inr h28 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h29
          -- Conjunctions on the left can always be decomposed.
          let h30 := h29.left
          let h31 := h29.right
          -- Conjunctions on the left can always be decomposed.
          let h32 := h30.left
          let h33 := h30.right
          -- One of the premise coincides with the conclusion.
          exact h33
      case inr h34 =>
        -- False on the left can always be used.
        apply False.elim h34
  case inr h35 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h36
    -- Conjunctions on the left can always be decomposed.
    let h37 := h36.left
    let h38 := h36.right
    -- Conjunctions on the left can always be decomposed.
    let h39 := h37.left
    let h40 := h37.right
    -- One of the premise coincides with the conclusion.
    exact h40



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249666548975402634507065013114 : ((p5 ∨ p4) ∨ ((((p2 ∧ p1) ∧ p3) ∨ (((p2 → p5) → (((p3 ∧ (p5 → p2)) ∧ True) → p5)) ∧ ((p3 ∧ p4) ∧ p1))) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328306282905496983389548222536 : (True → ((p5 ∧ ((p5 → (p3 → ((p3 ∧ (((p4 ∨ p3) ∨ (p5 ∧ (p4 ∨ p4))) ∨ p4)) ∨ p1))) ∨ True)) ∨ (p4 ∨ ((p3 ∨ p5) ∨ True)))) := by
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
theorem thm_5_vars_18092816463903976506645487057 : (((p3 ∨ ((p2 → False) ∧ ((((p1 ∧ False) ∧ True) ∨ (p4 ∨ (((False → True) ∧ p2) ∨ p4))) ∧ True))) ∨ (True ∨ (p5 ∧ (True ∧ p2)))) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46842920820810789596017648272 : (((((((p2 ∧ p4) → p5) → p1) ∧ ((p5 → (False → p5)) → ((((False ∨ True) → (p4 ∨ p5)) → p1) → p5))) ∧ p3) ∨ (True ∧ p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_213682190416433866731771213333 : ((((p5 → False) ∨ p5) ∨ p4) ∨ (((p1 ∧ p5) ∧ (((True ∨ (p2 ∨ (p4 ∨ p3))) ∨ (p1 ∧ False)) ∨ False)) ∨ (p1 → ((True ∧ p1) ∧ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172132530123108638496179211395 : ((((p4 ∨ (p2 ∧ p1)) ∨ ((p1 ∧ True) ∧ (p1 → p1))) ∧ ((p4 ∧ p2) ∧ p3)) ∨ (((True ∧ p1) ∧ (p1 ∧ p4)) → ((p2 → p4) ∨ p5))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h8
  -- One of the premise coincides with the conclusion.
  exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40192024730554262506605564627 : ((((((p5 → p5) → p1) ∨ (p2 → ((((((p5 ∨ p2) ∨ (p2 ∨ False)) ∨ p4) ∨ (p4 ∨ (True → p5))) ∧ p1) ∨ p5))) ∧ p1) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165602060250474388384357602003 : (((((False → (p4 → p1)) ∨ p2) → (p1 ∧ p3)) → ((p5 ∧ p2) ∨ (p3 → (p5 ∨ p5)))) ∨ (p3 ∨ (((p3 ∨ True) ∧ p2) ∨ (p5 → p5)))) := by
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
theorem thm_5_vars_172332317587587358026315839340 : (((((p2 → p5) ∨ p1) ∨ (p3 ∨ p3)) ∧ ((p1 ∨ False) ∧ ((p4 ∧ p1) ∧ p2))) ∨ (False ∨ (p4 → ((((p4 ∨ p5) ∨ True) → p2) ∨ p4)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52081116261991951863064259167 : ((((p2 ∨ ((p2 → p1) ∨ (p2 ∨ ((p5 → (p3 ∨ (p1 → False))) ∨ p2)))) ∧ p1) → ((p1 → p4) → (p4 → ((p3 ∧ p4) ∨ True)))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  cases h4
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
      -- Disjunctions on the left can always be decomposed.
      cases h9
      case inl h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h11 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48506209416125030991879744034 : ((((((p3 → (p3 → ((((p5 → p4) ∧ p4) → True) ∧ (p1 → (p5 → p5))))) ∧ (p2 ∨ p1)) → p1) ∨ p5) ∧ ((False ∨ p1) ∧ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65573560632580712162459773065 : ((p3 ∨ (p4 → (((False ∨ p1) ∧ p4) → (p3 ∨ ((False ∨ p5) ∨ ((p5 ∧ ((False ∧ (p2 ∧ (p2 ∨ True))) → (p5 → True))) → p2)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680287522036563258347567850407 : ((((((p4 ∧ (True ∧ ((p4 ∧ True) ∧ (False ∧ (p5 → (p5 → p3)))))) → p1) ∧ (True ∨ (False ∧ p2))) → ((p5 → p2) ∨ (p2 ∧ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60360065159378146345513512301 : (((p2 → p5) → ((p3 ∧ p3) ∨ ((p5 ∧ p5) → (((((p5 ∨ p4) ∨ ((p2 → (p4 → (True ∧ True))) ∧ True)) ∨ p1) ∨ p5) → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_259849463256362411780819899341 : ((p1 → p3) → (p5 → ((p5 ∨ p2) ∧ ((((((p2 ∧ p3) ∧ (p3 → (p1 ∨ False))) ∨ p5) ∧ (p3 → ((p5 ∧ p5) ∧ p5))) ∨ False) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_157217801165663493718771446337 : ((((((p5 ∧ ((p5 ∨ p5) ∧ (False ∨ (p4 → True)))) → p3) ∨ p3) ∨ ((p2 ∧ p3) ∧ True)) → p5) ∨ (False → (p1 ∧ ((p3 ∧ p4) → p2)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_606749395296117460355474039842 : ((((((p2 ∨ ((((((p1 ∨ p2) → ((p4 ∧ (p4 ∧ (p2 ∨ False))) ∨ p4)) ∧ True) ∧ p5) ∧ p1) ∧ True)) ∨ (p1 ∧ p1)) ∧ p1) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_774375084278272423332730298724 : (((False ∨ ((False ∨ ((((p4 ∧ p3) ∨ p5) ∨ (p2 → (p4 ∧ (((p3 → True) ∨ True) ∧ True)))) ∨ False)) ∨ (((False → p1) ∨ p4) ∧ False))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_43533058391099921195845662649 : ((((p1 → (p4 ∧ (p3 → (p5 ∨ ((((False → False) ∧ p3) ∨ (((p2 ∨ (p5 → True)) ∨ True) ∧ p2)) ∧ (p1 → False)))))) ∨ False) → p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310883424327594570311287006949 : (p2 ∨ ((p5 ∨ (p5 ∧ True)) → ((p3 ∧ (p2 → ((p1 ∨ (((p1 → ((True ∨ False) ∨ p3)) → p5) ∨ (p2 → (p4 ∧ p2)))) ∨ p1))) ∨ p5))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2
  case inr h3 =>
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148118008070575174670773949288 : (((((True ∨ (p4 ∧ (True ∧ p4))) ∨ p5) → (((p4 ∨ (p1 ∨ p5)) ∨ (p3 ∧ False)) ∨ p4)) → (False ∧ p2)) ∨ (p5 → ((p1 ∧ p3) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248596606152457377485526465862 : ((p3 ∨ False) ∨ ((p3 ∧ True) → ((p5 ∧ ((False ∨ p1) ∧ ((((p4 ∨ (p5 ∧ True)) → p4) → p4) ∨ (p2 → (p5 ∧ p3))))) ∨ (p1 ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_66076265589209088021320386888 : ((p5 ∨ ((p3 ∧ (((True → ((p2 ∧ False) → ((p1 ∨ p2) → False))) ∧ (p3 ∨ (p3 → ((p2 ∧ (p5 ∨ p2)) ∨ p2)))) ∨ p1)) ∨ True)) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149687453116572112164610825239 : ((p5 ∧ ((False ∨ (((p4 → ((p2 ∨ p2) ∧ ((p5 → (p3 ∨ True)) → p5))) → p1) ∧ p3)) ∨ (p4 ∧ p5))) ∨ (((p1 ∨ p4) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586941411630477504557106520510 : (((((p2 ∨ (((p1 ∧ (p1 ∧ (((True ∧ ((False ∨ True) ∨ p1)) → False) → False))) → p2) ∧ (p1 → (p2 → (False → True))))) ∧ p1) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318642935558722657780991869850 : (p4 ∨ ((p2 ∨ ((False ∨ ((((p2 ∨ True) ∨ True) ∨ p4) → (((p5 ∧ ((True → False) ∨ p1)) ∧ True) → p4))) → (p4 ∨ p2))) ∨ (p3 → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257248426460006149642975447954 : ((p2 ∨ p3) → ((p4 ∧ (((((p4 ∧ False) → False) ∧ p4) ∨ ((((p3 ∧ p3) → p3) ∨ (False ∨ p3)) ∧ ((p3 ∨ True) → p4))) → p1)) ∨ True)) := by
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
theorem thm_5_vars_313289214023225414970445215913 : (p3 ∨ ((p4 ∧ ((p1 ∨ p3) ∨ (((False ∨ p1) ∨ (True ∧ (p4 ∧ ((p2 → (p4 ∧ (p4 → True))) → p4)))) ∨ (p4 → (p1 ∨ p2))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_223993946527563579374962195421 : ((p4 ∨ (False → p1)) ∧ (((((p4 → (p4 ∧ (((p4 ∧ p2) ∧ True) ∨ (p3 → p2)))) → p2) ∧ False) ∨ ((True ∧ (p3 ∧ False)) ∨ True)) ∨ p4)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_638714843791029766496599346203 : ((((((False ∨ p5) ∧ ((p2 ∨ True) ∨ p5)) → (((True ∨ ((((True ∨ p5) ∨ (True → (p5 → p3))) → False) ∨ p5)) → p2) → True)) → p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342390327343206539114986747173 : (p2 → (((((((False → p4) ∨ True) → p3) ∨ p4) ∧ p2) ∧ ((p3 → (p1 → False)) ∨ False)) ∨ (p5 → (True ∨ ((True ∧ p1) ∧ (True ∧ p1)))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165940796180340187122382881281 : (((False ∨ p3) ∧ (p2 ∧ (p3 ∧ (p2 ∧ (p5 → (True ∨ (False ∧ (False ∧ (p4 ∧ p3))))))))) ∨ (False ∨ (p1 → (((p3 ∧ p1) ∨ p4) → p1)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h6 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_720457508385036478418749716469 : (((((p5 ∧ (p2 ∧ p4)) ∨ p3) → (True ∧ ((p2 ∧ ((p3 → p1) ∨ p1)) → ((((p5 ∧ False) → ((p5 ∧ p1) ∨ p2)) ∧ p5) → False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173103924160092350192813188925 : ((p1 ∨ (p4 → ((False → False) ∧ (p5 → (p2 ∨ (False ∨ ((p3 ∧ p3) ∨ False))))))) ∨ ((p5 → p1) ∨ (True ∧ ((True ∨ False) ∨ (False ∨ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617703425616141051275420693277 : ((((((p1 → (False → p2)) → (True → p5)) ∨ (((p1 → (p3 → (True → (True ∧ p2)))) → (((True → p3) ∧ p4) ∨ p1)) → p4)) ∨ p1) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69294491901190736908511795704 : ((p5 → (True ∧ (p2 → ((((True ∧ p5) ∧ (p1 ∧ (((p2 ∧ False) ∧ True) → (p4 ∨ (p1 → ((True → p4) → p2)))))) → p4) ∧ p5)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190340355018091727597689144732 : ((((p5 ∧ (False ∨ p1)) ∧ ((p2 ∧ p3) → True)) ∨ p2) ∨ ((True → (((True ∨ True) ∧ ((p5 ∨ p2) → (True ∨ True))) ∧ (p1 ∨ False))) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_704958203488088295926410855380 : ((((True → (((True ∧ p4) ∨ (p5 ∧ (False → p4))) ∨ True)) → (((p5 ∧ p1) ∧ ((p2 ∨ ((p4 ∨ False) ∨ p1)) → p5)) ∨ (p1 ∨ True))) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_137752500084243252208915824932 : ((p2 ∨ (((False ∧ p5) ∨ ((p5 ∨ (p5 ∧ ((p1 ∧ (((p1 ∧ p1) → p5) ∧ (p5 → p3))) ∨ p3))) ∨ p1)) ∨ True)) ∨ ((p1 ∨ p5) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_344365020424705283555327133969 : (p2 → (p4 ∨ ((((p2 ∧ (p2 → ((p5 ∨ p3) ∧ False))) ∧ (p4 ∨ ((p2 ∧ p2) → p2))) ∨ (p4 ∨ False)) ∨ (((p2 ∨ p5) → p1) → p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h3 : (p2 ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h4 := h2 h3
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137747699234459519518988404254 : ((p2 ∨ ((p4 ∨ (p4 → (p5 ∨ ((p1 ∨ (p1 ∧ p5)) ∧ ((p1 ∨ p2) ∨ (((p1 → False) → p5) ∧ False)))))) ∧ p4)) ∨ ((p1 ∨ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_603872749803067288143907827555 : ((((p4 ∨ (p2 ∨ ((False ∨ (True ∧ p4)) ∧ ((p2 ∨ ((p1 → (False ∨ (((p4 ∧ (p3 → False)) → True) ∨ p4))) → p3)) → p2)))) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_22288157560269293840961154530 : (((((p5 → (p5 ∧ (True ∨ p3))) ∨ p5) ∨ p1) → ((p2 ∧ ((p4 → p4) ∨ p2)) ∨ (p5 ∨ ((p5 → p4) ∨ (p4 → (True → True)))))) ∧ True) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h4
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
  case inr h7 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753605342883343431896893063215 : (((False ∧ ((p2 → ((((p1 → ((p3 → (p3 ∨ True)) → p5)) → p3) ∧ (p1 ∨ p5)) ∨ p4)) ∧ (p4 ∨ (((False ∧ False) ∧ True) ∨ p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_246135102106654902788453161873 : ((p4 ∧ p2) ∨ ((False ∨ (((((p5 ∨ p5) ∨ p1) ∨ ((p2 → False) → (p1 ∧ (p4 → (p4 → (True → (p1 ∨ p1))))))) ∨ False) ∧ p5)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113782278588799699681299881965 : ((((p5 → (p5 → p1)) ∨ (p1 → ((p4 ∧ (p2 ∨ (((False → False) ∧ p3) ∨ False))) → ((False ∧ True) → False)))) → (p4 ∧ p1)) ∨ (False → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42290352903572474327094083834 : (((p2 ∧ (((p2 ∧ ((((p1 ∨ (p1 ∧ (p3 ∧ False))) ∧ False) ∨ (p3 → (False → p1))) ∨ p4)) ∨ ((p2 → False) → p5)) ∧ p2)) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_803674002937676377158974891730 : (((p3 → ((p2 ∨ (((p3 ∧ (((p5 ∨ (((p2 → (True ∨ p3)) ∧ p1) ∧ p3)) → True) ∨ p4)) ∨ (p4 → (p2 ∧ p4))) → p3)) → p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159054515585894057633829934921 : ((p5 ∨ (((((False → p3) ∧ ((True ∨ True) ∨ True)) ∧ p2) → (p5 ∧ p2)) ∨ ((p4 ∧ p1) ∧ False))) ∨ (p2 → (True ∨ ((p2 ∨ False) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_328129053560439540490595165918 : (True → ((((p4 ∧ p4) ∧ False) ∧ ((p1 → p3) → (True ∧ (((p5 ∧ False) ∨ ((p3 ∧ p1) → p1)) → (p4 ∨ False))))) ∨ ((True → p1) → True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_681877665481462765708266140722 : (((((p4 ∨ ((((True → p3) → (p3 → p2)) ∧ (p4 ∨ ((p1 ∧ p5) ∧ p2))) ∧ p1)) ∧ False) ∧ ((((False → False) → p3) ∧ p2) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46937103937876774622060847759 : ((((p3 ∧ ((p3 ∨ p4) ∧ ((p3 ∧ (p1 → (((True ∧ p5) ∧ True) ∨ ((True ∧ True) ∧ p1)))) ∨ (True → p4)))) ∨ p5) ∨ (p3 → p4)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76491919244086037711275574767 : ((((True ∧ ((p2 ∨ (p4 ∨ p5)) ∨ (((p1 ∨ ((p3 ∧ p1) ∧ False)) → ((p5 ∧ p3) ∧ p1)) → False))) ∨ (p4 ∨ (True ∨ p5))) → False) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((True ∧ ((p2 ∨ (p4 ∨ p5)) ∨ (((p1 ∨ ((p3 ∧ p1) ∧ False)) → ((p5 ∧ p3) ∧ p1)) → False))) ∨ (p4 ∨ (True ∨ p5))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44536898243314934479591759148 : (((((((p3 ∧ p5) ∧ p5) → p5) ∨ ((p1 ∨ p5) ∧ p1)) → (((p1 ∨ p1) ∨ (((p3 → (p3 → True)) → p2) ∧ p2)) → False)) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115274617140876043159931185190 : (((p1 ∨ ((p1 ∨ p5) ∨ (p4 ∨ ((p3 → p5) ∨ p5)))) ∨ (((False → (False ∧ p1)) ∨ p2) ∨ (True ∧ ((p5 ∨ True) ∨ True)))) ∨ (p2 ∧ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_644113991891970138957047298998 : ((((True ∨ ((p5 ∨ False) → ((((p5 ∧ ((p2 ∧ True) → ((False ∨ (p3 → p4)) ∧ p5))) ∨ (p2 → p4)) ∨ (p3 ∧ p5)) ∨ p5))) → p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



