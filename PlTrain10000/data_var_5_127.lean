variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_142616946691802993546257018207 : ((False ∨ (True ∧ (((p5 ∧ ((p2 ∨ ((p1 ∧ False) ∧ (((True ∨ p4) ∨ True) ∧ p2))) ∨ (p2 ∨ True))) → p3) ∧ p1))) → (p3 ∨ (p4 → p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h7



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_938021742217190175179169678577 : ((((p5 ∨ (p1 → ((p3 ∨ False) → p4))) ∧ ((p4 → ((((p5 ∧ ((False → p5) ∨ True)) → p3) ∧ (False ∧ p2)) ∧ (p5 ∨ p2))) ∧ p4)) → p5) ∧ True) := by
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
    -- One of the premise coincides with the conclusion.
    exact h4
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h3.left
    let h9 := h3.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h10 : p4 := by
      -- One of the premise coincides with the conclusion.
      exact h9
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h10
    -- We need to get the left conjuct of h11 based on <expert-advice>.
    let h12 := h11.left
    -- We need to get the right conjuct of h12 based on <expert-advice>.
    let h13 := h12.right
    -- We need to get the left conjuct of h13 based on <expert-advice>.
    let h14 := h13.left
    -- False on the left can always be used.
    apply False.elim h14
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255953263083904887585114413355 : ((True ∨ p2) → (False ∨ (False ∨ ((p1 → ((p4 ∧ (p2 ∨ p4)) ∨ ((p4 ∨ (p5 ∨ (False ∧ p5))) → (False → (True → p5))))) ∨ (True → True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h5
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42509310303854724558842589687 : (((False ∨ (((False ∨ False) ∨ False) ∧ ((((True ∧ False) → (p2 ∧ (p1 ∨ p1))) ∧ (p3 → ((p2 → p5) ∧ (p1 ∨ p5)))) ∨ True))) ∨ True) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_114690069090629037206938140741 : (((p2 → ((True ∧ ((p5 → (False ∨ (p3 → p4))) ∨ ((p4 ∨ False) ∧ p5))) ∧ True)) ∨ (((p1 ∨ p5) ∨ p4) ∧ (p2 ∨ p2))) ∨ (True ∨ False)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137902471963351947519642727480 : ((p4 ∨ (((((p5 ∧ (False ∨ p5)) ∧ p4) → (p5 ∨ ((p3 ∨ p4) ∧ p2))) → p1) ∨ (((p4 → p4) → p1) ∧ False))) ∨ ((True ∧ True) ∧ True)) := by
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318199238480750807403982653750 : (p4 ∨ (((((((p1 → p3) ∨ p1) ∧ (True ∨ p3)) ∨ (p4 ∨ (p2 → p3))) ∨ True) → (((True ∧ p4) ∧ (p2 → (True ∧ False))) ∧ p1)) → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p1 → p3) ∨ p1) ∧ (True ∨ p3)) ∨ (p4 ∨ (p2 → p3))) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- We need to get the right conjuct of h3 based on <expert-advice>.
  let h4 := h3.right
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_206329411832408074022975370027 : ((p1 ∨ (True → (p3 → (False ∧ p1)))) ∨ (p1 → (((((True ∨ p1) ∨ False) ∧ p3) ∨ True) ∧ (False ∨ ((p1 ∨ (False → (True → p1))) ∨ False))))) := by
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_118130461908947343557248066603 : ((False ∨ ((((p4 ∨ ((False ∧ p3) ∨ ((True ∧ (True ∧ p5)) → (False → p4)))) ∧ (p5 → p4)) ∧ p5) ∧ (p2 ∧ (p2 ∨ p5)))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_336324761520433313331538158291 : (p1 → (((p4 ∧ (p5 → False)) ∧ ((((p5 ∨ p5) → p5) ∧ p5) → ((False ∨ p5) → ((True → (p3 → (False → p4))) → (p1 ∧ p3))))) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38037650294381528743717923004 : (((((((p1 ∨ (p5 → p4)) → ((False ∧ True) → p1)) ∧ ((p4 ∨ ((p3 → (p5 → p4)) ∨ p2)) ∨ False)) ∨ True) → (p5 ∧ p1)) ∧ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_339873973158030709141268802675 : (p1 → (True → ((p4 ∧ (p3 → (p4 ∨ p4))) ∨ ((p3 ∧ ((p4 → (p1 → False)) ∧ p3)) → ((True ∧ ((p4 ∧ True) → (p5 ∨ False))) ∨ p5))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h8
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h11 : p4 := by
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h12 := h6 h11
  -- We want to use the implication h12 based on <expert-advice>. So we show its premise.
  have h13 : p1 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h12, we can now drive its conclusion.
  let h14 := h12 h13
  -- False on the left can always be used.
  apply False.elim h14



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66166207055173277592207047702 : ((p5 ∨ (((((True → ((p3 ∧ (p4 ∧ p2)) ∨ p1)) ∨ True) ∨ (p2 ∧ (False ∧ p1))) ∨ (True ∧ (p2 ∧ p4))) ∨ ((False → True) ∨ False))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788717063372830741755835236700 : (((p5 ∨ (((False → ((False → p3) ∨ p2)) ∧ ((((p1 ∨ (p3 ∨ False)) ∧ (p4 ∨ False)) ∨ True) ∨ ((p1 ∨ p2) → (p4 ∨ p5)))) → p5)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_740481056711721197302947503910 : ((((p1 ∨ p5) ∨ ((False → (p1 → ((((p5 ∨ (p2 ∨ p2)) → (((p2 ∨ p5) → p2) → False)) ∨ (p5 ∨ True)) ∧ p1))) → (p2 ∧ p4))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349987203109382566237602279054 : (p4 → ((((((((((p2 ∨ (p4 ∧ (((p1 → p4) → p4) ∧ p5))) → p2) ∧ p5) ∨ p3) ∨ p2) ∨ p2) ∨ p4) → (p5 ∨ False)) ∨ True) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_88261870878256868442892952992 : (((p3 ∨ (False → (p3 ∨ True))) ∧ ((((((p1 ∨ p3) ∨ p2) ∨ False) ∨ True) ∨ (p3 ∨ p4)) → (((p1 ∧ p3) ∧ (p2 ∧ p5)) ∨ False))) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h5 : (((((p1 ∨ p3) ∨ p2) ∨ False) ∨ True) ∨ (p3 ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h5
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h7 =>
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h8.left
      let h11 := h8.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h9.left
      let h13 := h9.right
      -- One of the premise coincides with the conclusion.
      exact h10
    case inr h14 =>
      -- False on the left can always be used.
      apply False.elim h14
  case inr h15 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h16 : (((((p1 ∨ p3) ∨ p2) ∨ False) ∨ True) ∨ (p3 ∨ p4)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h17 := h3 h16
    -- Disjunctions on the left can always be decomposed.
    cases h17
    case inl h18 =>
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h19.left
      let h22 := h19.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h20.left
      let h24 := h20.right
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h25 =>
      -- False on the left can always be used.
      apply False.elim h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_607059875649806132732551442335 : (((((((p1 ∨ (p2 ∧ (p2 ∧ ((p3 ∧ p5) ∧ p4)))) ∨ p5) ∧ (p4 ∧ ((p1 ∧ True) ∨ (p5 ∨ (p2 ∨ (True → False)))))) ∧ False) ∨ True) ∨ p4) ∧ True) := by
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
theorem thm_5_vars_47938269681359148682840349485 : ((((((((False → (p2 ∨ (p4 ∧ p4))) → (p2 → p4)) ∨ (p1 → (p2 → p4))) ∨ p1) → p1) ∨ (True ∧ (p5 ∨ p4))) → (p2 ∨ p1)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148214873289064905521075369219 : (((p3 → (p3 → (((p2 → p2) → (p2 ∧ (((True → p3) → p2) ∧ p1))) ∨ p4))) ∧ (p2 ∧ (False → p4))) ∨ (((True → True) ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_774371637384682550553819402840 : (((False ∨ ((True ∧ (((p2 ∨ ((p5 ∧ p5) → ((p4 ∨ p1) ∧ ((p5 → p3) ∧ p5)))) → p1) ∨ p5)) ∨ ((p5 ∧ p5) ∧ (False ∧ p3)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_778910278841585718243330661544 : (((p1 ∨ (p1 → ((p3 → p2) ∧ (((False ∨ ((p1 ∧ p5) ∧ p4)) ∨ ((((p3 ∧ p1) ∨ (p2 ∧ p1)) → (False ∨ p2)) → False)) ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308395657446959379111781937572 : (p2 ∨ (((False ∧ (((((p5 ∨ (p4 → ((False ∧ (False ∨ p5)) → p2))) ∨ p3) → p4) ∧ p4) ∨ (((p2 ∧ p1) ∨ True) ∨ p1))) ∨ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_300266038134277360789121564794 : (False ∨ ((False ∨ (((p3 ∨ True) ∨ (p3 → True)) → ((((p4 ∨ p5) ∧ (((p2 ∨ p4) ∨ (False → p4)) → p2)) → p2) → False))) → (p1 ∧ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : ((p3 ∨ True) ∨ (p3 → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h5 := h3 h4
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h6 : (((p4 ∨ p5) ∧ (((p2 ∨ p4) ∨ (False → p4)) → p2)) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h8
      case inl h10 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h11 : ((p2 ∨ p4) ∨ (False → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h10
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h12 := h9 h11
        -- One of the premise coincides with the conclusion.
        exact h12
      case inr h13 =>
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h14 : ((p2 ∨ p4) ∨ (False → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h15
          -- False on the left can always be used.
          apply False.elim h15
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h16 := h9 h14
        -- One of the premise coincides with the conclusion.
        exact h16
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h17 := h5 h6
    -- False on the left can always be used.
    apply False.elim h17
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h18 =>
    -- False on the left can always be used.
    apply False.elim h18
  case inr h19 =>
    -- We want to use the implication h19 based on <expert-advice>. So we show its premise.
    have h20 : ((p3 ∨ True) ∨ (p3 → True)) := by
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h19, we can now drive its conclusion.
    let h21 := h19 h20
    -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
    have h22 : (((p4 ∨ p5) ∧ (((p2 ∨ p4) ∨ (False → p4)) → p2)) → p2) := by
      -- Implications on the right can always be decomposed.
      intro h23
      -- Conjunctions on the left can always be decomposed.
      let h24 := h23.left
      let h25 := h23.right
      -- Disjunctions on the left can always be decomposed.
      cases h24
      case inl h26 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h27 : ((p2 ∨ p4) ∨ (False → p4)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- One of the premise coincides with the conclusion.
          exact h26
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h28 := h25 h27
        -- One of the premise coincides with the conclusion.
        exact h28
      case inr h29 =>
        -- We want to use the implication h25 based on <expert-advice>. So we show its premise.
        have h30 : ((p2 ∨ p4) ∨ (False → p4)) := by
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h31
          -- False on the left can always be used.
          apply False.elim h31
        -- We have shown the premise of h25, we can now drive its conclusion.
        let h32 := h25 h30
        -- One of the premise coincides with the conclusion.
        exact h32
    -- We have shown the premise of h21, we can now drive its conclusion.
    let h33 := h21 h22
    -- False on the left can always be used.
    apply False.elim h33



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164614573395957176523578972273 : (((p3 ∧ ((p1 ∨ (((((p3 ∨ (p3 ∨ p1)) ∧ p2) ∧ p2) ∧ p5) ∨ p2)) → p3)) ∧ False) ∨ ((p2 → (False → (True → p5))) ∨ (p3 ∨ p1))) := by
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
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50200217851171894800025340420 : ((((((((p3 ∧ (p1 → (((p1 → p2) ∧ p1) ∧ (p1 → p1)))) ∨ p2) → p3) ∨ False) ∧ True) ∨ p4) ∨ ((p3 ∧ (False ∧ p2)) ∧ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134044218538075218120493644799 : (((((p2 ∧ p3) ∧ (p5 ∨ (((p1 → (p5 → (p5 → p4))) → p3) → ((p4 → p3) → (p5 → True))))) ∨ p1) ∨ p5) ∨ (p4 → (p2 ∨ p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53722133455592221860713018602 : (((True → ((False ∨ ((p5 ∧ p3) ∧ (False → p3))) ∨ p5)) ∧ (((True ∧ True) ∨ (p5 ∨ ((False ∨ ((p1 ∧ p2) ∨ p1)) ∨ p4))) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_194210967737802931507398186548 : ((p3 → ((p5 ∧ True) ∧ (True ∧ ((p1 → p2) ∨ p1)))) → (p5 ∨ ((True ∨ (((((p4 ∨ p4) → p5) ∧ False) ∨ (True ∧ False)) → p2)) ∧ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_177840480699588091555485770235 : ((((((p5 → False) ∧ p2) ∨ ((p1 → p3) ∨ (p3 → p1))) ∧ p2) ∨ False) ∨ ((False → (True → (((False ∨ p1) ∧ p4) → False))) ∨ (p2 ∨ p3))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h4 := h3.left
  let h5 := h3.right
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_208222095655807987235432052810 : (((p5 → (p4 → p1)) → (p1 → p3)) → ((p3 → ((((p4 ∧ p1) → (True ∨ True)) → (p3 ∨ ((p4 → False) ∧ p4))) → p3)) ∧ (True ∨ False))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_588076635396127728927536036773 : (((((((((p4 ∨ p3) ∧ True) ∧ (p4 ∧ (False ∨ ((True → False) ∨ p1)))) ∨ False) ∨ (((p4 ∧ (False → p2)) ∨ p3) ∧ p1)) ∨ p1) ∧ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37956792855867169426096224970 : (((((p4 → (((p1 ∧ True) ∨ (p3 ∨ False)) ∧ (p5 → (p1 ∧ ((p3 ∧ p2) ∧ (False → (p2 ∧ p5))))))) ∧ p5) ∨ (p4 ∧ p5)) ∧ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76806973130474738253530828130 : ((((((p1 ∨ (((p3 → (True → p1)) → p3) ∨ False)) ∧ p3) ∨ True) ∨ ((True ∧ (p2 ∨ False)) ∨ ((p3 ∧ (True ∧ p1)) ∧ p1))) → False) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((((p1 ∨ (((p3 → (True → p1)) → p3) ∨ False)) ∧ p3) ∨ True) ∨ ((True ∧ (p2 ∨ False)) ∨ ((p3 ∧ (True ∧ p1)) ∧ p1))) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_70876316728800517935243483171 : ((((((((p3 → (p4 ∧ p1)) ∧ (p4 ∨ p3)) ∨ False) ∧ p2) ∨ True) → ((False ∨ p1) ∧ ((p4 → p4) → (False ∧ (p1 → True))))) ∧ p5) → False) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (((((p3 → (p4 ∧ p1)) ∧ (p4 ∨ p3)) ∨ False) ∧ p2) ∨ True) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
  have h7 : (p4 → p4) := by
    -- Implications on the right can always be decomposed.
    intro h8
    -- One of the premise coincides with the conclusion.
    exact h8
  -- We have shown the premise of h6, we can now drive its conclusion.
  let h9 := h6 h7
  -- We need to get the left conjuct of h9 based on <expert-advice>.
  let h10 := h9.left
  -- False on the left can always be used.
  apply False.elim h10



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_253054857937309904468559520455 : ((True ∧ p4) → (((((p4 → p5) ∧ (((((p2 ∧ False) ∨ (True → False)) ∨ (p1 → (True → False))) ∨ p4) → False)) ∨ (p3 → p4)) → False) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54943515732565576472119396080 : (((((p3 ∧ p3) → p2) ∧ (p1 ∨ False)) ∧ ((p4 ∧ True) ∧ ((p4 ∨ ((p3 ∨ p2) ∧ p3)) ∧ (((p3 ∨ p2) ∧ p4) ∨ (p2 ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_129068059806974408085645013218 : ((((((False ∨ False) → ((True → ((p5 ∧ False) ∧ ((p4 → p3) → ((True → p3) ∨ p3)))) ∧ False)) → p1) ∨ True) ∨ p1) ∧ ((p1 ∧ p2) → p2)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_248714264646607741058001634781 : ((p3 ∨ p2) ∨ ((p3 ∧ (p3 ∨ p3)) → (((p2 → p5) → ((p5 → ((p1 ∨ (p2 ∨ p5)) ∨ (p2 → (p5 ∨ p5)))) ∨ True)) ∨ (True ∧ False)))) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h5
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h6 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h7
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_184615353005411135990515272181 : (((((p3 → p2) → True) ∧ (p1 ∧ p5)) ∧ (True → (False ∧ p5))) ∨ (p5 → (p5 → ((p5 ∧ (p1 ∨ (p5 → ((False → p4) → p5)))) ∨ p3)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_324942370361335768056047090632 : (p5 ∨ ((p2 ∨ p3) ∨ ((False ∧ ((((p2 ∧ p3) ∨ (p5 → (p3 ∨ p2))) → p5) → (p1 ∧ ((False → (p1 → p4)) ∨ (p4 → p1))))) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_122596192789930990958880942615 : (((((((p5 ∧ p2) ∨ p4) ∨ (((p2 ∧ p2) ∨ p2) → (p4 ∨ (False ∧ p2)))) ∨ ((p5 → True) ∨ p4)) ∨ p5) → (p2 ∧ False)) → (p4 ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((p5 ∧ p2) ∨ p4) ∨ (((p2 ∧ p2) ∨ p2) → (p4 ∨ (False ∧ p2)))) ∨ ((p5 → True) ∨ p4)) ∨ p5) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196697575259418192563695065426 : ((((p3 ∧ (p2 ∨ (False ∨ p3))) ∨ p4) ∧ False) ∨ (p4 → ((p3 ∨ (False ∨ (p4 ∧ True))) ∨ (p5 ∧ (((p4 → (p2 ∨ p2)) ∨ p5) ∧ p3))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_227890525152746544567847450818 : ((p2 ∧ (False → False)) ∨ (False ∨ ((((False ∨ p1) ∨ (((True → (((True ∨ (p4 → p1)) ∨ True) ∧ p5)) ∧ p2) ∨ True)) ∧ True) ∧ (True ∨ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_322404761570472913193448028239 : (p5 ∨ ((((False → p5) ∧ (True ∧ (p2 ∧ (p1 ∧ ((p5 ∧ p3) → p4))))) ∨ (False ∨ ((p2 ∨ (((p3 ∧ False) ∧ p3) → p2)) → p4))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205486036888375329510746222649 : (((False ∧ p4) ∧ ((False ∨ False) ∨ p5)) ∨ ((p1 ∧ p5) ∨ (False ∨ ((True → ((p2 ∨ p1) ∨ ((p2 ∧ p1) ∨ (p2 ∧ (p3 ∧ p3))))) ∨ True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247914298125309962790856901093 : ((p1 ∨ p3) ∨ ((((((False ∨ ((p3 ∧ p5) ∨ p3)) ∧ p2) ∨ True) ∨ True) ∧ (True ∧ True)) ∨ (((p4 → p4) ∨ p3) → ((p3 ∨ p4) ∧ p5)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745740611552000252525719523057 : ((((True ∨ p5) → (p4 → ((((p2 → ((p3 ∧ p2) → (p2 ∧ False))) → p2) ∨ ((p4 ∨ (p4 → p1)) ∨ (False ∧ True))) → (p1 ∨ False)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_351518950663099598086749760908 : (p4 → ((((p5 ∨ ((p3 ∨ (p3 → ((p5 ∧ True) → p2))) ∨ ((p1 ∧ True) → p5))) ∧ p5) ∨ p1) ∨ ((False ∧ ((False ∨ True) ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_112367532252958634353440490276 : ((((((True ∨ (((p2 ∧ False) ∧ True) ∧ p2)) → (False ∧ ((False ∨ (p1 ∧ p2)) ∧ ((p2 ∧ True) ∧ p1)))) → True) ∧ p2) → p1) ∨ (p3 → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354781281093921306309886403297 : (p5 → ((((False ∨ False) → (p5 ∧ (p2 ∧ (p4 → p2)))) ∧ ((((p2 ∨ p5) ∧ (p1 ∨ (p2 ∨ p4))) → (False ∧ (p5 → p3))) ∨ p5)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h5 =>
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  -- Implications on the right can always be decomposed.
  intro h7
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h8 =>
    -- False on the left can always be used.
    apply False.elim h8
  case inr h9 =>
    -- False on the left can always be used.
    apply False.elim h9
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_247711581778965711061238331603 : ((p1 ∨ False) ∨ ((((False ∧ p4) ∧ ((((p2 ∨ False) → (p4 ∨ p2)) ∨ ((p4 → True) → (p4 → p5))) → p1)) ∨ (p5 ∨ (p1 ∨ True))) ∨ p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_41804756481854463491746810626 : ((((True → (p2 ∧ (p4 ∧ p3))) → (p5 → (((((p2 ∨ p3) ∧ p5) ∨ p4) → p1) ∨ (p5 → (p4 ∨ ((p5 → p1) ∨ p1)))))) ∨ p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51308730462151833405831234775 : (((p2 ∨ ((p4 → p3) ∧ ((p4 ∧ ((p3 ∧ p1) ∨ (p3 ∨ ((p2 ∨ p2) ∧ True)))) → p2))) ∨ ((p4 → p1) → ((p1 ∨ False) ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191374087301016482082103819474 : (((p1 → p2) ∨ ((((True ∨ p4) ∨ p5) → p5) ∧ p3)) ∨ (((p2 ∧ ((p2 ∧ p4) ∧ (p1 ∧ (((p4 → True) ∨ p3) ∧ p3)))) ∨ p2) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_326917895703478755659678174669 : (True → ((((False ∨ ((((p2 → p4) ∧ (p3 ∨ p5)) ∧ p4) ∧ p5)) ∨ ((p3 ∨ p1) ∨ (p1 ∨ (p3 → (p4 → (p5 ∧ p5)))))) → p3) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135067410223396792385840566810 : ((((((True ∧ (p2 ∨ p1)) → ((False ∧ ((p5 → (p5 ∨ p4)) → p2)) ∧ p1)) ∨ p3) ∧ (True ∧ p5)) ∨ (p3 ∨ p3)) ∨ ((p3 → True) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_53215095134767769634554544510 : ((((p5 ∧ (True → ((p1 → p2) → False))) ∨ ((p3 ∨ False) ∧ p1)) ∨ ((p5 ∧ ((p1 → p2) ∧ p1)) ∨ (True → (p1 → (p1 ∨ True))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_725801877460587409138006788214 : (((((p4 ∨ p1) ∧ p2) ∨ (((((((True → (p5 ∨ True)) ∧ (p3 → p4)) ∧ True) → ((p2 ∧ (p5 ∨ p2)) → p5)) ∧ p4) ∨ p2) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_198635873878461022513805820896 : ((p3 ∨ (((True → (p3 ∧ False)) ∨ p4) → p2)) ∨ ((p2 → (p2 ∨ ((False → (p1 → (p3 ∨ p3))) ∨ p4))) → (p5 ∨ (p1 ∨ (p2 ∨ True))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_118117811516315597044236049207 : ((False ∨ (((p3 ∨ p1) → (((p1 ∨ (((False ∧ p3) ∨ p1) → (p2 → (p2 ∧ (p4 ∧ p3))))) ∧ p2) ∨ (True ∧ p5))) → p2)) ∨ (p4 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254635673208678257194922339781 : ((p3 ∧ p2) → ((((((p3 → p4) → False) ∧ p3) ∧ p5) ∨ (((p5 ∧ False) ∧ p5) ∨ (p5 ∧ (p4 ∧ (p2 ∧ ((p4 ∨ p4) → p5)))))) ∨ True)) := by
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
theorem thm_5_vars_147909153934947574703458601502 : (((((((((True → False) ∨ p1) ∧ p4) ∨ p5) ∧ (p3 ∧ (p3 → p2))) ∧ False) ∧ (p3 ∨ p4)) ∧ (p2 → p1)) ∨ ((p4 ∨ p2) → (p3 ∨ True))) := by
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
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_108062532490321025485986241667 : (((True ∨ True) → ((((p1 ∨ (p3 ∧ True)) ∨ p4) ∨ (False ∧ (p1 → p2))) → (p4 → (False ∨ ((True ∨ (True ∨ p5)) ∨ False))))) ∧ (p3 → p3)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Disjunctions on the left can always be decomposed.
      cases h5
      case inl h6 =>
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h7 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h8 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
      case inr h9 =>
        -- Conjunctions on the left can always be decomposed.
        let h10 := h9.left
        let h11 := h9.right
        -- Disjunctions on the left can always be decomposed.
        cases h1
        case inl h12 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
        case inr h13 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- True on the right can always be proven directly.
          apply True.intro
    case inr h14 =>
      -- Disjunctions on the left can always be decomposed.
      cases h1
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h16 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h17 =>
    -- Conjunctions on the left can always be decomposed.
    let h18 := h17.left
    let h19 := h17.right
    -- False on the left can always be used.
    apply False.elim h18
  -- Implications on the right can always be decomposed.
  intro h20
  -- One of the premise coincides with the conclusion.
  exact h20



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_212761743525313054459198003692 : ((p1 → ((p4 ∧ False) → True)) ∧ ((((True ∧ p3) ∨ (((p5 → (False → p5)) ∧ (p3 ∧ (p1 ∨ (p5 → p2)))) → p5)) ∨ p1) ∨ (p2 → p2))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h3
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135215651681744646728352683870 : (((((p1 ∨ (True ∨ (p3 ∧ True))) ∨ ((p1 ∨ (False → p4)) → p5)) ∧ (p3 → (p1 ∨ (p5 ∧ True)))) → (p2 ∨ False)) ∨ (False → (p2 → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_27141001164790265455161664226 : (((p2 → False) ∨ (((((p5 ∨ (p2 ∨ p4)) ∨ p2) → (p2 ∧ ((p5 ∨ True) → p3))) ∨ (p3 ∨ ((p5 ∧ (p5 ∨ False)) ∧ p4))) ∨ True)) ∧ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37738717232507699382816773519 : ((((((p3 → ((True ∨ p3) → (p4 ∧ p1))) → p5) ∧ (True → (((p4 ∧ p1) → ((p1 ∧ p1) ∧ p1)) ∧ (p2 → p4)))) → p5) ∧ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_266193340986516695975938011909 : (True ∧ (p4 → (((True ∧ ((p4 ∧ ((p3 ∨ (p1 ∨ (True → (True ∧ True)))) ∧ (True ∨ (p2 → (p4 ∨ True))))) ∧ True)) ∧ p2) → (False ∨ p2)))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
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
  let h7 := h6.left
  let h8 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h7.left
  let h10 := h7.right
  -- Conjunctions on the left can always be decomposed.
  let h11 := h10.left
  let h12 := h10.right
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h13 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h14 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h15 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h4
  case inr h16 =>
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h19 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h20 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4
      case inr h22 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111387489220234925300883121349 : (((False ∨ (p1 ∧ (p4 ∧ (True → ((((False ∨ (True → (((p2 ∧ False) ∨ p5) ∨ p1))) → False) ∨ (p1 ∨ p2)) → False))))) ∧ p1) ∨ (p3 → p3)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_612277733165088963298848558498 : ((((((p3 ∧ p5) → (p3 ∧ (p4 ∨ (True ∧ ((p1 ∧ p5) ∨ (((False ∧ True) → ((False → p1) ∨ p5)) ∧ p1)))))) ∧ (True → p1)) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_185229744899649705444522120674 : ((False ∧ ((p2 → (p1 ∨ (p3 ∨ p4))) ∨ (p2 → (p2 ∧ p5)))) ∨ (p5 → ((p2 ∧ (p5 → p3)) → (p3 ∨ ((False ∧ p5) ∨ (p3 ∨ p4)))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- We want to use the implication h4 based on <expert-advice>. So we show its premise.
  have h5 : p5 := by
    -- One of the premise coincides with the conclusion.
    exact h1
  -- We have shown the premise of h4, we can now drive its conclusion.
  let h6 := h4 h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193817710948725787521956344194 : ((p5 ∧ ((p1 ∨ ((p2 ∨ True) ∨ True)) → (False ∨ False))) → (False ∧ ((((((p5 → p2) → False) ∧ p1) → (True ∧ False)) ∨ p3) ∨ (p1 ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
  have h4 : (p1 ∨ ((p2 ∨ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h3, we can now drive its conclusion.
  let h5 := h3 h4
  -- Disjunctions on the left can always be decomposed.
  cases h5
  case inl h6 =>
    -- False on the left can always be used.
    apply False.elim h6
  case inr h7 =>
    -- False on the left can always be used.
    apply False.elim h7
  -- Conjunctions on the left can always be decomposed.
  let h8 := h1.left
  let h9 := h1.right
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h10 : (p1 ∨ ((p2 ∨ True) ∨ True)) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h11 := h9 h10
  -- Disjunctions on the left can always be decomposed.
  cases h11
  case inl h12 =>
    -- False on the left can always be used.
    apply False.elim h12
  case inr h13 =>
    -- False on the left can always be used.
    apply False.elim h13



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314406995285514139582718115755 : (p3 ∨ (((((p2 ∨ False) ∧ True) → ((p3 ∨ p5) → (((p2 ∧ p2) ∨ p1) ∧ (p1 ∧ (p1 ∧ p1))))) ∨ p2) ∨ (((p3 ∧ True) ∨ True) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42900396553991805694669321401 : (((p3 → ((p3 ∨ (False → (((False → p1) ∧ p4) ∨ p5))) → ((((p4 → p4) → p5) ∨ p5) ∨ (False → ((p4 → False) → p5))))) ∨ False) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
theorem thm_5_vars_327221048722678114765365654728 : (True → ((p1 → (False ∨ ((((p2 ∨ p1) → (p5 → (True → (((p1 ∨ True) → p2) → p1)))) → ((p5 → (p2 ∨ p3)) → p5)) ∨ p4))) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_57041971740326866819373620353 : (((p3 → (False ∧ False)) ∧ (((((p4 → (p1 ∧ p5)) → p5) ∨ p1) ∧ (((p3 ∧ p3) → True) ∨ p2)) → (False ∨ ((p1 ∨ True) ∧ p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40520105657458060034000086620 : ((((p5 ∧ ((p5 ∧ p5) ∨ ((((p5 → (((p3 ∨ p1) ∨ True) → p2)) → (False ∧ (p2 ∨ p5))) ∨ False) ∨ (p4 ∧ p3)))) ∨ p3) ∨ False) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264348602163729098165077420087 : (True ∧ (((False ∧ p3) ∨ (False → p4)) ∧ ((False → False) → ((p3 ∧ True) → (True → (p5 ∨ ((((True ∧ p3) → p5) ∨ p3) ∨ (p2 ∧ True)))))))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the left can always be decomposed.
  let h5 := h3.left
  let h6 := h3.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_316381471232705713980352201559 : (p3 ∨ (False ∨ (((((((p4 ∧ p5) ∨ (((p2 ∧ (p2 ∧ p2)) → True) ∧ p1)) → False) ∧ False) ∧ p5) ∨ (True ∨ True)) ∨ (True ∧ (p4 ∧ p4))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
theorem thm_5_vars_50252689194416691967984406666 : (((((p2 ∨ p1) → (((p5 ∧ (p3 ∨ p2)) → False) ∨ (p3 ∨ ((p2 → p3) ∧ (p1 ∧ p5))))) → p1) ∨ ((p2 ∧ (False ∨ p1)) ∧ p5)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_245475734287224154308605530632 : ((p2 ∧ p5) ∨ ((((((((p2 ∨ p2) → (p2 ∨ True)) ∧ p1) ∧ (((p2 ∧ True) ∧ p1) → p3)) ∧ p4) ∧ False) ∨ (p1 ∨ p1)) ∨ (False ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_323236789107222478190214042409 : (p5 ∨ ((((False ∧ p1) ∧ p4) ∨ (((p2 ∧ (p2 ∨ (p4 ∨ (p4 ∨ True)))) ∨ (p5 → ((True ∨ p3) ∧ p5))) ∨ (p1 ∧ False))) ∨ (True → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66144848080575982617697096756 : ((p5 ∨ ((p1 ∨ (False ∧ (p3 ∨ ((p3 ∨ p2) ∨ (p4 ∧ (p5 → (((p2 ∧ p5) ∨ ((p4 ∧ p3) → p1)) ∨ p4))))))) ∨ (p4 → True))) ∨ p1) := by
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
theorem thm_5_vars_215890776669612453633209345471 : ((p3 ∨ ((p2 ∧ False) ∨ p2)) ∨ (((p4 ∨ (p2 → (((((p1 ∨ p4) ∧ True) → p5) ∧ p3) → ((p1 → p3) ∨ (p4 ∧ p1))))) ∧ True) ∨ p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352865593654197022554194171876 : (p4 → (True ∧ ((((p4 ∨ (p4 ∧ (False ∧ (p2 ∨ False)))) ∨ (p5 ∨ (p5 → p2))) → (p3 → ((False ∧ (p1 ∨ (p1 ∧ True))) ∨ True))) ∨ p1))) := by
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
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- Disjunctions on the left can always be decomposed.
    cases h4
    case inl h5 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h6 =>
      -- Conjunctions on the left can always be decomposed.
      let h7 := h6.left
      let h8 := h6.right
      -- Conjunctions on the left can always be decomposed.
      let h9 := h8.left
      let h10 := h8.right
      -- False on the left can always be used.
      apply False.elim h9
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
theorem thm_5_vars_151146615915120564811296149597 : ((((p1 → (False ∧ (p3 → (((p2 ∧ p5) ∧ (((p5 → p5) ∧ p5) → False)) ∨ p1)))) → (p4 ∨ p4)) → p4) → ((p4 ∧ (True → p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_64156106308698957718221420504 : ((False ∨ ((p1 ∧ p2) ∧ (((False ∨ (True ∨ (True ∧ (False ∧ p3)))) → (((((p4 ∧ p3) ∨ p2) → p4) → p1) ∨ p4)) ∧ (p1 → p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_802194719993758062449187167122 : (((p2 → (p2 ∧ ((p3 ∧ (((p5 ∨ True) → p2) → ((p2 ∧ (True ∧ (p5 ∨ p4))) → (p1 ∧ False)))) ∧ (p3 ∨ (False ∨ (True → False)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37893754555058040868992229957 : (((((False → (((p5 ∧ (p4 ∨ p2)) ∧ ((p5 ∨ p2) ∧ (False → ((p3 ∧ (p3 → p5)) ∧ False)))) → p3)) → p1) ∧ (p4 ∨ False)) ∧ p4) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49914254643735936113838105354 : ((((((p1 ∧ (p1 → (((p3 ∧ True) ∨ p5) ∨ p3))) → ((p3 ∧ p2) ∧ p5)) ∨ (p1 ∧ p3)) → p4) ∧ ((p4 → p1) ∧ (p1 ∨ p4))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51198750198664576558662651631 : ((((p3 ∨ (((p4 ∨ p2) ∨ p5) ∨ ((p2 → p1) ∨ p1))) ∧ (False ∨ (p3 ∧ (p3 → p1)))) ∨ (True → ((p3 → (p4 → True)) ∨ p3))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_335709441573111241583712123919 : (p1 → (((p1 ∧ (((p5 ∨ (p2 → False)) ∨ True) → (p4 ∨ (((True ∧ (p3 ∧ p3)) ∨ p5) → ((True ∨ (p4 ∧ False)) → False))))) ∨ p1) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_232962402252466136606175173411 : ((p3 ∧ (True → False)) → (((p2 ∧ p1) ∧ p4) ∨ (((p2 ∧ ((True ∧ (p1 → True)) → p2)) ∨ (True ∨ False)) ∧ (p3 ∧ (p2 → (p1 ∨ False)))))) := by
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
theorem thm_5_vars_174540096140358568691439173479 : (((p2 ∧ ((False ∧ (p3 ∧ p2)) ∧ p2)) → (p4 ∨ (p3 ∧ ((p5 ∨ True) ∨ False)))) → (((p4 ∧ ((p5 ∧ p2) → p5)) → p1) ∨ (True ∨ p1))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354619906203720070077947234019 : (p5 → ((((p1 ∧ ((True ∨ p4) ∨ p4)) ∨ (((p4 ∨ p2) ∨ (((p3 ∨ (False ∨ (p2 ∧ p3))) ∧ False) ∨ (p1 → p4))) ∨ True)) ∨ p3) ∨ False)) := by
  -- Implications on the right can always be decomposed.
  intro h1
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
theorem thm_5_vars_192932818255711688901725662254 : (((((p1 → p3) ∧ p2) ∧ (p2 ∨ p5)) ∨ (p2 ∧ p4)) → (p3 → ((((((True ∧ False) ∧ (p4 → p4)) ∨ p5) ∨ (p1 ∨ p1)) ∨ p1) ∨ p3))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h2
    case inr h9 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h9
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116498800061375453857894896534 : (((p3 ∧ p2) ∧ ((False ∨ p1) ∧ (((p4 ∧ False) ∧ ((p1 ∨ (p4 ∧ p3)) → (p2 ∧ True))) ∧ ((p4 → (p4 ∨ p5)) → p2)))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350028209288051314223292879886 : (p4 → (((((((p2 ∨ ((True → p2) ∧ (((p3 ∧ p3) ∨ False) → p3))) → (p1 ∧ p1)) ∨ False) → p2) ∨ (True → (p3 → p4))) → p1) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_191611653856326466599129507777 : ((p3 ∧ ((p5 ∨ (True ∨ p1)) ∧ ((p5 → p1) ∨ p1))) ∨ ((p5 ∧ p4) → (((((p4 → True) ∧ p2) → False) ∨ (p5 ∧ (p5 ∨ p3))) ∨ p2))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



