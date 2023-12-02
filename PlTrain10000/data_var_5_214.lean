variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158895149683939601292067398182 : ((p1 ∨ (((((True → p4) → (p1 ∨ False)) → (p2 ∨ (p3 → False))) ∧ ((p2 ∧ p3) ∨ p1)) ∨ True)) ∨ ((p1 → (p3 → p5)) ∧ (p5 → p1))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135471369341556451070637929873 : ((((((p5 ∨ True) ∧ ((p3 → p5) → (p2 ∨ (p4 ∨ p3)))) ∨ False) → ((True ∧ p1) ∨ False)) → ((p2 → p2) → p3)) ∨ (p3 ∨ (p5 ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158989768339933911354552270833 : ((p3 ∨ ((False ∨ p4) ∨ (p4 → (((False ∨ (p3 ∧ p3)) → True) ∧ (((p4 ∧ p5) → p2) → p1))))) ∨ (p5 ∨ (((p3 ∨ p5) ∧ p1) ∨ True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_304759059310727423634704072616 : (p1 ∨ ((False ∧ (((((p3 → ((p5 ∧ (False ∧ p2)) ∨ (False ∨ (p3 ∧ p5)))) ∧ (p1 ∨ (True ∨ True))) ∧ p4) ∧ p2) ∧ False)) ∨ (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354264017721305319888384829957 : (p5 → ((((((p2 ∨ False) ∧ ((((p1 ∧ (p1 → p1)) ∨ (((p1 ∨ False) ∨ p1) → p1)) ∧ p3) ∧ True)) → p4) → p3) ∨ (True ∧ p5)) ∧ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- One of the premise coincides with the conclusion.
  exact h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_40198691463898419937537173475 : (((((False ∧ False) ∧ (p4 ∧ ((((p3 ∨ p1) ∨ p5) → p5) ∨ ((True ∨ p5) → (p2 ∧ ((p2 → (p4 → p5)) ∧ p5)))))) ∧ p3) ∨ True) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134224721644161182134476739830 : ((((p2 ∨ (((True ∧ p1) ∧ p5) ∧ p2)) ∨ (p4 ∧ (((True ∨ p4) ∨ p5) ∧ (p2 ∨ ((False → p1) → p1))))) ∨ False) ∨ (True ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44811262042258799317440051555 : ((((p3 ∧ (p4 → p5)) ∧ ((p2 ∨ ((p2 → (p1 → ((p2 → p1) → False))) → (p4 ∨ p3))) → (False ∨ ((p2 → p3) → p1)))) → p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_917300645768823680910097796377 : ((((((p4 → ((False → ((p4 ∧ True) ∧ p1)) → (p2 ∨ p3))) → (p2 → False)) → True) → ((p3 ∧ ((p3 ∧ p1) ∧ (p3 ∧ False))) ∧ p2)) → False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 → ((False → ((p4 ∧ True) ∧ p1)) → (p2 ∨ p3))) → (p2 → False)) → True) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the left conjuct of h4 based on <expert-advice>.
  let h5 := h4.left
  -- We need to get the right conjuct of h5 based on <expert-advice>.
  let h6 := h5.right
  -- We need to get the right conjuct of h6 based on <expert-advice>.
  let h7 := h6.right
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- False on the left can always be used.
  apply False.elim h8
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358019746459802523933461763606 : (p5 → (False ∨ (p4 ∨ (((p1 ∨ (p2 ∨ ((p5 ∨ p3) → ((p4 ∧ p4) ∧ True)))) ∨ ((((p3 → (p4 ∧ p2)) ∨ p3) ∧ p5) ∨ p1)) ∨ p5)))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314094670233192817558145244067 : (p3 ∨ (((((p5 ∧ ((False ∧ p3) ∧ p1)) → False) → (p2 ∧ False)) ∧ (p2 ∨ (((True → (p4 ∨ (p5 → p5))) → p1) → p1))) → (p2 → False))) := by
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
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h6 : ((p5 ∧ ((False ∧ p3) ∧ p1)) → False) := by
      -- Implications on the right can always be decomposed.
      intro h7
      -- Conjunctions on the left can always be decomposed.
      let h8 := h7.left
      let h9 := h7.right
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Conjunctions on the left can always be decomposed.
      let h12 := h10.left
      let h13 := h10.right
      -- False on the left can always be used.
      apply False.elim h12
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h14 := h3 h6
    -- We need to get the right conjuct of h14 based on <expert-advice>.
    let h15 := h14.right
    -- False on the left can always be used.
    apply False.elim h15
  case inr h16 =>
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h17 : ((p5 ∧ ((False ∧ p3) ∧ p1)) → False) := by
      -- Implications on the right can always be decomposed.
      intro h18
      -- Conjunctions on the left can always be decomposed.
      let h19 := h18.left
      let h20 := h18.right
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Conjunctions on the left can always be decomposed.
      let h23 := h21.left
      let h24 := h21.right
      -- False on the left can always be used.
      apply False.elim h23
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h25 := h3 h17
    -- We need to get the right conjuct of h25 based on <expert-advice>.
    let h26 := h25.right
    -- False on the left can always be used.
    apply False.elim h26



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187594736586873516473637860068 : ((p4 ∨ ((((p3 → p1) → (p5 ∨ p2)) → (True → p5)) ∧ p5)) → (True → ((p5 ∨ (p5 ∨ (False ∧ (p2 ∧ p3)))) ∨ (p4 ∨ (p4 ∨ True))))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  case inr h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_47587913475534271579233084140 : (((p2 → (((p3 ∧ ((False ∧ p2) ∧ (p5 ∧ p1))) ∧ True) ∨ (((p3 ∨ p4) ∨ (p3 ∧ (p4 ∧ (p4 ∧ p5)))) ∧ p3))) ∨ (p1 → p1)) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_753732979286496257199130956382 : (((False ∧ (((p2 → (p3 ∨ (False → (p3 ∨ p5)))) ∧ (False → (p2 ∧ p5))) ∧ (p4 ∧ (p4 → ((p5 ∨ (p4 ∧ (True ∨ p4))) → p5))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178809168924505604418678617458 : (((True ∧ (p5 ∧ p5)) ∨ (True → (((p4 → False) ∨ (p5 ∧ True)) ∨ p3))) ∨ ((((p1 ∨ p4) ∧ False) → p4) ∨ (((p5 ∨ p2) → p2) ∧ p4))) := by
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
    apply False.elim h3
  case inr h5 =>
    -- False on the left can always be used.
    apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_201245254313176908970519914084 : ((p3 → ((p2 ∧ (p4 → (False → p5))) ∧ p4)) → (((p5 ∨ (False ∨ p1)) → p3) → (p5 → ((p1 ∨ ((p3 ∧ (p5 ∨ p2)) ∧ p4)) ∨ p1)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
  have h4 : (p5 ∨ (False ∨ p1)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h3
  -- We have shown the premise of h2, we can now drive its conclusion.
  let h5 := h2 h4
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h6 : p3 := by
    -- One of the premise coincides with the conclusion.
    exact h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h7 := h1 h6
  -- We need to get the right conjuct of h7 based on <expert-advice>.
  let h8 := h7.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h3
  -- One of the premise coincides with the conclusion.
  exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_394220791213194373856457026270 : (((((p4 ∧ True) → ((p3 ∧ (p1 ∧ p1)) ∨ (p1 ∨ (p3 ∨ ((((p5 ∧ False) → (True → p1)) ∨ (p3 ∨ p4)) ∨ (p3 ∨ p2)))))) ∨ p4) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_762271349170645672424510595375 : (((p3 ∧ ((False ∨ ((False ∨ ((False → (True → (((p1 ∧ p5) ∧ False) ∨ (p5 ∨ p3)))) ∨ (False ∨ p5))) → (p2 → p1))) → (p4 → p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156822381238560790188050436259 : (((p4 ∨ ((((p1 ∨ True) → (p5 ∨ p3)) ∧ p3) ∧ ((((p2 ∨ p3) → p1) → p2) ∧ p3))) ∧ p1) ∨ (p1 → (p5 → (False → (p3 ∨ p3))))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134155309404544248295670376951 : ((((p4 → (((True ∧ ((p4 → p4) → ((p3 ∧ p1) ∨ p2))) ∧ True) ∧ (False ∧ False))) ∨ (p1 ∧ (p3 ∨ p2))) ∨ True) ∨ ((p4 ∧ p5) ∧ True)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59354526044636536680945908209 : (((p5 ∨ p1) ∨ (p1 ∨ (p5 ∧ (p5 ∨ (p1 ∨ (p3 ∧ (True → ((False ∨ p4) → (((p2 ∨ p5) ∧ ((p1 → p2) ∧ p5)) ∨ p1))))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_9207967073853415517063975225 : ((((p2 ∨ (p3 ∧ (p4 ∨ ((p4 ∨ (p4 ∧ p3)) ∨ p5)))) → (((p3 ∧ p2) ∨ (p3 ∨ True)) ∨ (((p3 ∨ True) → p2) ∧ p1))) ∨ p2) ∧ True) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    case inr h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h7
      case inl h8 =>
        -- Disjunctions on the left can always be decomposed.
        cases h8
        case inl h9 =>
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h4
        case inr h10 =>
          -- Conjunctions on the left can always be decomposed.
          let h11 := h10.left
          let h12 := h10.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h12
      case inr h13 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_257623376219552593098447538408 : ((p3 ∨ p2) → (((p3 ∨ (p5 → (((p4 ∧ ((False ∨ p5) → (p5 ∧ (p1 ∨ p2)))) → p1) → p5))) ∨ ((p4 → p1) → p1)) → (p1 ∨ True))) := by
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
      cases h1
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      case inr h9 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h1
    case inl h11 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h12 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139496493244620028753913474203 : (((((((True ∨ (p5 ∧ ((((True ∨ p3) ∨ False) ∨ p1) ∨ p1))) ∧ (p3 ∨ p5)) → p4) ∨ (p1 ∨ False)) → p4) → True) → ((p2 → False) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_669754484862334656858952917437 : (((((((p5 → ((p5 → (True ∨ p1)) ∧ p4)) → (p4 → p4)) → (p1 ∧ p2)) ∨ ((p4 → (p3 ∧ p2)) ∧ p2)) ∨ ((p3 ∧ p4) → p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172444493592125102105105717500 : ((((False ∨ (p5 → p2)) ∨ p2) ∨ (((p4 ∧ False) → (False ∨ p4)) → (p5 ∧ p2))) ∨ ((True ∧ (p5 ∨ (p3 → (False → (p3 → p3))))) ∨ p4)) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342019193612132197421956701471 : (p2 → ((True → ((p1 ∨ ((((((p5 ∧ p5) ∧ p1) → False) → p4) → (p5 ∧ ((p5 ∨ p4) → p5))) ∨ False)) ∨ True)) ∨ ((p4 → True) ∨ p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_84938788120363076470164359222 : ((((((p1 ∧ (False ∧ p1)) ∨ (False ∨ True)) ∧ (False ∨ True)) → (False ∧ p1)) ∨ ((True ∨ (False ∨ (p1 → ((p1 ∨ False) ∧ p4)))) ∧ p1)) → p1) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h3 : (((p1 ∧ (False ∧ p1)) ∨ (False ∨ True)) ∧ (False ∨ True)) := by
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
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h4 := h2 h3
    -- We need to get the left conjuct of h4 based on <expert-advice>.
    let h5 := h4.left
    -- False on the left can always be used.
    apply False.elim h5
  case inr h6 =>
    -- Conjunctions on the left can always be decomposed.
    let h7 := h6.left
    let h8 := h6.right
    -- Disjunctions on the left can always be decomposed.
    cases h7
    case inl h9 =>
      -- One of the premise coincides with the conclusion.
      exact h8
    case inr h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h8



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_617556152790241643603864385517 : (((((False ∧ ((True → (p2 → p1)) ∧ False)) ∧ (((p5 ∨ ((p3 ∧ p1) → p4)) ∧ p2) ∨ (False ∧ (((True ∨ p1) ∨ p2) ∨ p2)))) ∨ True) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_62456223208752795659873823404 : ((p3 ∧ ((p2 ∧ p2) ∧ (((p3 ∨ p5) ∧ p4) ∨ ((p3 ∨ (((p5 → p3) → p3) ∧ (True ∧ p5))) ∧ (p1 ∧ (False ∧ (True ∨ p2))))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310484057518983370359430816688 : (p2 ∨ ((((True ∧ p3) ∧ (p2 ∧ p5)) ∧ p5) ∨ (((((False ∨ p5) ∨ p5) → (p5 ∧ False)) → (False ∨ ((p2 ∧ p2) ∨ p4))) ∨ (p1 → True)))) := by
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
theorem thm_5_vars_199668498651976723308706102928 : ((((p2 ∧ p5) ∨ ((True → p5) ∧ p1)) → p1) → (((((True ∨ p3) → True) → ((p2 ∨ False) ∧ p2)) ∧ (p4 → (p2 ∧ p4))) ∨ (False → p3))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172936993862851166044880355619 : ((p3 ∧ (((((True ∧ p4) ∨ (p1 ∧ p5)) ∨ p5) → p2) ∨ (p3 ∨ (p5 ∧ False)))) ∨ (p5 ∨ (p2 ∨ ((False → (p2 → (True → p1))) ∨ p4)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135129344194755960484122184448 : (((p2 ∧ (((True ∨ True) → p1) → ((p4 ∨ (p3 ∧ ((p3 ∨ True) ∧ p3))) → (p2 ∨ (p5 ∨ p5))))) ∨ (p1 → p3)) ∨ ((True ∧ False) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_352040804679915327449989523371 : (p4 → (((p1 ∨ p3) → (p5 ∨ ((False ∨ p2) ∨ p3))) → (((p3 ∧ ((p3 → p3) → False)) ∨ p1) → (((False ∧ (p1 → p5)) ∨ p1) ∧ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- We want to use the implication h6 based on <expert-advice>. So we show its premise.
    have h7 : (p3 → p3) := by
      -- Implications on the right can always be decomposed.
      intro h8
      -- One of the premise coincides with the conclusion.
      exact h8
    -- We have shown the premise of h6, we can now drive its conclusion.
    let h9 := h6 h7
    -- False on the left can always be used.
    apply False.elim h9
  case inr h10 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h10
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_51071852574115709407690202304 : (((p2 → ((((p3 ∧ (p3 → p2)) ∧ p5) → p4) → (((p3 ∧ (p5 ∨ True)) ∨ p3) → p1))) ∧ ((False ∨ p2) ∨ (p3 ∨ (p2 ∧ p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_165169673055179744595042341491 : (((True ∧ (p1 ∧ (p5 ∨ (True → ((((p3 ∨ p5) ∨ p4) ∨ p4) ∧ p4))))) ∧ (p2 ∧ p5)) ∨ (p3 ∨ (p4 ∨ (False → ((p2 ∧ p2) → p2))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_670000021108310064023726493521 : ((((((True ∧ ((False ∧ (True ∧ False)) → p3)) ∨ p4) ∧ ((((p5 ∧ p4) ∨ (p5 ∧ p3)) ∧ p2) ∧ (p2 ∨ False))) ∨ (True ∧ (p3 → True))) ∨ p3) ∧ True) := by
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
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_217829189429656078730903166916 : (((p4 ∨ (True ∧ p3)) → p3) → (((p1 ∨ ((True → p3) → p4)) ∨ (((p4 ∧ p1) ∧ ((((p2 ∨ False) → p4) ∨ p2) ∧ False)) ∧ p3)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135950038942878592479897510934 : ((((((p1 ∨ p4) ∨ p2) ∧ True) → ((p4 ∨ p5) ∧ p3)) ∧ (p3 → (((p1 ∨ (p4 ∨ True)) ∧ p2) ∧ (p3 ∧ p1)))) ∨ ((True ∨ p4) ∧ True)) := by
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
theorem thm_5_vars_4234393890489492201176558118 : (p5 ∨ ((p4 ∧ ((p4 ∧ False) ∨ p1)) ∨ (((p2 ∧ p5) → p2) ∧ (p3 ∨ ((p3 → (p1 ∨ True)) → ((p5 → p5) ∧ (p5 → p5))))))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h5
  -- One of the premise coincides with the conclusion.
  exact h5
  -- Implications on the right can always be decomposed.
  intro h6
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_181211719946773539074464167435 : ((p2 ∧ ((p2 → p1) ∧ (p3 → (p2 ∧ (((False → True) ∧ p2) ∧ p4))))) → ((((True ∨ True) ∧ (p2 ∧ p1)) ∨ True) ∧ (p2 → (p1 ∨ p1)))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h6
  -- Conjunctions on the left can always be decomposed.
  let h7 := h1.left
  let h8 := h1.right
  -- Conjunctions on the left can always be decomposed.
  let h9 := h8.left
  let h10 := h8.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
  have h11 : p2 := by
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h9, we can now drive its conclusion.
  let h12 := h9 h11
  -- One of the premise coincides with the conclusion.
  exact h12



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_41190634847811357566769825491 : (((((p3 ∧ ((p2 ∨ True) → (True ∧ p1))) → (p5 → (((p1 → (p3 → (p3 → p2))) → p2) ∨ p3))) → (p1 ∨ (p3 ∧ p1))) ∨ True) ∨ False) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_119301222239979340207124350140 : ((p3 → ((p1 → ((p5 ∨ (p3 ∧ ((((p1 ∧ p2) ∨ (p4 → False)) → False) → (False ∨ (True ∧ p3))))) ∧ (True ∧ p2))) → p1)) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_329689883418924533815397852478 : (True → ((p3 ∨ p4) → (((((p3 ∧ p1) ∨ ((True ∨ (p2 → ((p2 ∧ (True → (p5 ∧ p1))) ∧ p3))) → False)) ∧ (p3 → p4)) ∨ p2) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_777836593045804300385591360699 : (((p1 ∨ (((p4 ∧ (p1 → p2)) ∨ p3) ∨ (((p5 → (False ∨ False)) → p5) → (((p4 ∨ p5) ∨ (((p3 ∧ p2) → True) ∨ p2)) ∧ True)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_318557193902137120497211415265 : (p4 ∨ ((((((p3 → False) → (p1 ∨ (p1 → (p5 ∧ (p4 → p5))))) → (p3 ∨ p5)) ∧ ((p4 ∧ (True ∨ p2)) ∧ p3)) ∨ p1) ∨ (False → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_608529139042441991405963623489 : (((((((p2 ∧ p4) → (((p4 ∨ ((((p1 ∨ p4) ∧ True) ∨ ((False ∧ p1) → p3)) ∨ p3)) ∧ False) ∧ (p2 ∧ p4))) → p1) ∨ p5) ∨ p4) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_183873409613960473644218753129 : (((((p4 ∨ p3) ∧ p1) ∧ (p4 ∧ (p4 ∨ (p5 → p4)))) ∧ False) ∨ (p3 ∨ (p5 → ((p1 → p5) ∨ ((True → (p4 ∨ (True ∨ p1))) ∧ False))))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_788730619780870369216030268838 : (((p5 ∨ (((p2 ∨ (True ∧ True)) ∨ (True ∧ ((((p2 ∧ p5) → True) → ((((p4 ∧ False) → p3) → False) → (True ∧ p3))) ∨ p5))) → False)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_175318830283772496017069315467 : ((p4 ∨ (((p3 → ((p5 ∨ p5) → False)) → (p5 ∨ p2)) ∧ ((p1 ∧ False) → p5))) → ((p3 → p1) → (((False → True) → (p1 ∨ p5)) ∨ True))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h5 := h4.left
    let h6 := h4.right
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_682024989935282547669030010354 : (((((True ∧ ((False ∧ (p3 ∧ ((p1 → ((p1 ∧ (p1 ∧ False)) ∨ False)) → p1))) ∨ p1)) ∨ p4) ∧ (((False → p3) ∨ (p4 ∧ False)) ∧ True)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_159930059688359978602191154427 : (((((p1 → True) → (((((False ∨ p2) ∧ p2) ∧ p3) → (True → (False ∨ True))) ∧ p2)) → p2) → False) → ((p2 ∧ (False ∨ (p1 ∨ p4))) ∧ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p1 → True) → (((((False ∨ p2) ∧ p2) ∧ p3) → (True → (False ∨ True))) ∧ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h3
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h4 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h6 := h3 h4
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- One of the premise coincides with the conclusion.
    exact h7
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h8 := h1 h2
  -- False on the left can always be used.
  apply False.elim h8
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h9 : (((p1 → True) → (((((False ∨ p2) ∧ p2) ∧ p3) → (True → (False ∨ True))) ∧ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h10
    -- We want to use the implication h10 based on <expert-advice>. So we show its premise.
    have h11 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h12
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h10, we can now drive its conclusion.
    let h13 := h10 h11
    -- We need to get the right conjuct of h13 based on <expert-advice>.
    let h14 := h13.right
    -- One of the premise coincides with the conclusion.
    exact h14
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h15 := h1 h9
  -- False on the left can always be used.
  apply False.elim h15
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h16 : (((p1 → True) → (((((False ∨ p2) ∧ p2) ∧ p3) → (True → (False ∨ True))) ∧ p2)) → p2) := by
    -- Implications on the right can always be decomposed.
    intro h17
    -- We want to use the implication h17 based on <expert-advice>. So we show its premise.
    have h18 : (p1 → True) := by
      -- Implications on the right can always be decomposed.
      intro h19
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h17, we can now drive its conclusion.
    let h20 := h17 h18
    -- We need to get the right conjuct of h20 based on <expert-advice>.
    let h21 := h20.right
    -- One of the premise coincides with the conclusion.
    exact h21
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h16
  -- False on the left can always be used.
  apply False.elim h22



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_325986233529234947719409489998 : (p5 ∨ (True → (((((((True ∨ (((p4 ∨ False) → p1) ∨ (p3 ∧ p3))) ∧ p4) → p4) ∧ ((p5 ∨ p5) → False)) → p4) ∨ True) ∧ (False → True)))) := by
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
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_310131481035671693425341287365 : (p2 ∨ ((False ∧ (p1 ∧ ((p2 ∧ False) ∨ (p3 ∨ (p3 ∨ ((p1 → p4) ∧ p1)))))) ∨ (p3 → (((p2 → p3) → p2) → ((p5 ∧ True) → True))))) := by
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
theorem thm_5_vars_113173489218242058402466985055 : (((p5 → (p5 ∧ ((p2 → ((p1 → p2) ∧ ((p3 ∨ False) ∨ (True ∧ p5)))) → (((p2 ∨ p1) ∧ (True → p3)) ∧ p5)))) → p3) ∨ (p5 → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_156953206723655381874939500051 : (((((False → ((p4 ∨ (True → p2)) ∨ p4)) → ((p3 → False) ∧ p2)) ∧ (p1 ∨ (p5 → p4))) ∨ True) ∨ (p2 ∨ ((p2 ∧ p5) → (p5 → p4)))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50200010960549158217611803174 : (((((((p4 → (True ∧ (p5 → True))) ∧ ((False → p2) → (p5 ∨ (p1 ∨ p4)))) ∧ p1) ∧ False) ∨ p5) ∨ ((p5 → (p2 ∨ p4)) ∨ True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_691251003088516194144268671937 : ((((((p3 ∨ (p4 → p5)) ∧ p2) ∨ ((p4 ∧ (p5 ∧ (p2 ∨ p3))) ∧ (p2 ∨ True))) → (False ∨ (p5 → (((p4 → True) ∨ p3) ∧ p5)))) ∨ p3) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h6
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h5
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h7 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h8
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h9
      -- True on the right can always be proven directly.
      apply True.intro
      -- One of the premise coincides with the conclusion.
      exact h8
  case inr h10 =>
    -- Conjunctions on the left can always be decomposed.
    let h11 := h10.left
    let h12 := h10.right
    -- Conjunctions on the left can always be decomposed.
    let h13 := h11.left
    let h14 := h11.right
    -- Conjunctions on the left can always be decomposed.
    let h15 := h14.left
    let h16 := h14.right
    -- Disjunctions on the left can always be decomposed.
    cases h16
    case inl h17 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h18 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h19
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h20
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h19
      case inr h21 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h22
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Implications on the right can always be decomposed.
        intro h23
        -- True on the right can always be proven directly.
        apply True.intro
        -- One of the premise coincides with the conclusion.
        exact h22
    case inr h24 =>
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h26
      case inr h27 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h28
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- One of the premise coincides with the conclusion.
        exact h24
        -- One of the premise coincides with the conclusion.
        exact h28
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52900530060316941685056499929 : (((True → (True ∧ (p2 ∧ ((True → (p2 ∨ p2)) ∧ ((False → p3) → p1))))) → ((p3 → p5) ∨ (((p4 ∨ (p2 ∨ True)) → p1) ∧ p1))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h5 := h1 h4
    -- We need to get the right conjuct of h5 based on <expert-advice>.
    let h6 := h5.right
    -- We need to get the right conjuct of h6 based on <expert-advice>.
    let h7 := h6.right
    -- We need to get the right conjuct of h7 based on <expert-advice>.
    let h8 := h7.right
    -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
    have h9 : (False → p3) := by
      -- Implications on the right can always be decomposed.
      intro h10
      -- False on the left can always be used.
      apply False.elim h10
    -- We have shown the premise of h8, we can now drive its conclusion.
    let h11 := h8 h9
    -- One of the premise coincides with the conclusion.
    exact h11
  case inr h12 =>
    -- Disjunctions on the left can always be decomposed.
    cases h12
    case inl h13 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h14 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h15 := h1 h14
      -- We need to get the right conjuct of h15 based on <expert-advice>.
      let h16 := h15.right
      -- We need to get the right conjuct of h16 based on <expert-advice>.
      let h17 := h16.right
      -- We need to get the right conjuct of h17 based on <expert-advice>.
      let h18 := h17.right
      -- We want to use the implication h18 based on <expert-advice>. So we show its premise.
      have h19 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h20
        -- False on the left can always be used.
        apply False.elim h20
      -- We have shown the premise of h18, we can now drive its conclusion.
      let h21 := h18 h19
      -- One of the premise coincides with the conclusion.
      exact h21
    case inr h22 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h23 : True := by
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h24 := h1 h23
      -- We need to get the right conjuct of h24 based on <expert-advice>.
      let h25 := h24.right
      -- We need to get the right conjuct of h25 based on <expert-advice>.
      let h26 := h25.right
      -- We need to get the right conjuct of h26 based on <expert-advice>.
      let h27 := h26.right
      -- We want to use the implication h27 based on <expert-advice>. So we show its premise.
      have h28 : (False → p3) := by
        -- Implications on the right can always be decomposed.
        intro h29
        -- False on the left can always be used.
        apply False.elim h29
      -- We have shown the premise of h27, we can now drive its conclusion.
      let h30 := h27 h28
      -- One of the premise coincides with the conclusion.
      exact h30
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h31 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h32 := h1 h31
  -- We need to get the right conjuct of h32 based on <expert-advice>.
  let h33 := h32.right
  -- We need to get the right conjuct of h33 based on <expert-advice>.
  let h34 := h33.right
  -- We need to get the right conjuct of h34 based on <expert-advice>.
  let h35 := h34.right
  -- We want to use the implication h35 based on <expert-advice>. So we show its premise.
  have h36 : (False → p3) := by
    -- Implications on the right can always be decomposed.
    intro h37
    -- False on the left can always be used.
    apply False.elim h37
  -- We have shown the premise of h35, we can now drive its conclusion.
  let h38 := h35 h36
  -- One of the premise coincides with the conclusion.
  exact h38



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_225972509541532504726230279969 : (((p3 ∧ p2) ∨ False) ∨ ((p5 ∧ ((((p5 ∧ (p1 ∨ (p5 → False))) ∨ p1) ∨ (((p4 ∨ p2) → ((p2 ∨ p2) ∧ True)) → True)) → False)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_527901664804889246361676914 : ((((((p4 ∨ p5) ∧ (p4 ∧ ((p3 ∨ False) → p3))) ∨ (False ∧ (p4 ∨ (((True ∧ True) → (p3 ∨ True)) ∨ p1)))) ∧ p3) ∨ p5) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_613397493884439759589103938180 : (((((p2 ∧ (False → (p5 → ((False ∧ (False ∨ (((False ∧ p3) → p2) ∨ (True ∨ True)))) ∨ ((p5 ∨ p3) → p5))))) → (p1 ∨ False)) ∨ True) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_199168630219659850625355438330 : (((True ∧ (((p4 → p4) ∨ True) ∨ True)) ∧ True) → ((((((p3 → False) ∨ p4) ∨ True) ∨ (p2 ∨ (True ∨ True))) ∨ False) ∨ (p3 → (p2 ∨ False)))) := by
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
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h8 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h9 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_124520022501589188368874104167 : ((((p5 ∨ p1) ∨ (p5 ∨ (p1 ∧ p2))) ∧ (((True → p5) → (((True ∨ (p1 → p3)) → (p1 → p4)) → False)) → (True ∧ p4))) → (p4 ∨ True)) := by
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
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h9 =>
      -- Conjunctions on the left can always be decomposed.
      let h10 := h9.left
      let h11 := h9.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61066850635370699607720215494 : ((False ∧ (((p3 ∨ p5) → (((p1 ∧ (p1 ∨ (False ∧ (False ∨ p1)))) → (False ∨ (p4 ∧ p2))) ∧ (True ∧ p5))) ∨ (p5 ∨ (p4 ∨ p2)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52575839118087837089504891085 : (((((True ∨ (((True ∨ p3) ∨ (p1 → p4)) → p2)) ∧ p4) → (p1 ∧ p2)) ∨ (p5 ∧ ((False → False) ∨ ((p3 ∨ False) → (True ∧ p4))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_765817237330488856346322495881 : (((p4 ∧ ((p5 ∨ ((p5 → (p5 → True)) → (p3 ∧ p1))) → ((((p5 → ((p5 → p3) ∧ (p3 → p1))) ∨ p2) → p1) ∧ (False ∧ p5)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_674185878094932495485665337880 : ((((p4 ∧ ((False → p2) ∧ (((True ∨ (p2 ∧ p1)) → (p3 ∨ p1)) ∨ (False → ((p2 ∧ False) ∨ (p4 → True)))))) → (False ∧ (p3 ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_680574334267970257902152818781 : ((((((True → ((p4 ∨ (p3 → p4)) ∨ p1)) → p3) ∨ (p2 ∧ (((p3 → (p3 ∧ p3)) → p1) ∨ p1))) → (p5 ∧ ((p3 ∨ p4) → p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_153313423016910979992682342307 : ((p1 ∨ ((p3 ∧ p2) ∧ ((True ∧ (p5 ∨ p2)) → (((True ∧ p5) → (True ∧ ((False ∨ p1) → p3))) → p1)))) → ((p5 → False) ∨ (False ∨ p1))) := by
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
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Conjunctions on the left can always be decomposed.
    let h6 := h4.left
    let h7 := h4.right
    -- We want to use the implication h5 based on <expert-advice>. So we show its premise.
    have h8 : (True ∧ (p5 ∨ p2)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h7
    -- We have shown the premise of h5, we can now drive its conclusion.
    let h9 := h5 h8
    -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
    have h10 : ((True ∧ p5) → (True ∧ ((False ∨ p1) → p3))) := by
      -- Implications on the right can always be decomposed.
      intro h11
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Implications on the right can always be decomposed.
      intro h12
      -- Disjunctions on the left can always be decomposed.
      cases h12
      case inl h13 =>
        -- False on the left can always be used.
        apply False.elim h13
      case inr h14 =>
        -- Conjunctions on the left can always be decomposed.
        let h15 := h11.left
        let h16 := h11.right
        -- One of the premise coincides with the conclusion.
        exact h6
    -- We have shown the premise of h9, we can now drive its conclusion.
    let h17 := h9 h10
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h17



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_69234166692086874126414217275 : ((p5 → ((((p2 ∧ False) ∧ p1) → p4) → ((True → p3) → (p4 ∨ ((True ∨ (False → p3)) → (((False ∧ p2) → p1) → (False ∨ p3))))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Implications on the right can always be decomposed.
  intro h5
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h6 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h7 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h8 := h3 h7
    -- One of the premise coincides with the conclusion.
    exact h8
  case inr h9 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- We want to use the implication h3 based on <expert-advice>. So we show its premise.
    have h10 : True := by
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h3, we can now drive its conclusion.
    let h11 := h3 h10
    -- One of the premise coincides with the conclusion.
    exact h11



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_173928316519385698751926483882 : (((((p4 ∧ False) → (p1 ∨ (p2 ∨ (p4 ∨ (p1 ∨ True))))) ∨ (False ∨ p4)) → p1) → (((p2 ∨ ((p4 ∨ True) ∨ p5)) ∧ (p1 ∨ p4)) ∨ p3)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((p4 ∧ False) → (p1 ∨ (p2 ∨ (p4 ∨ (p1 ∨ True))))) ∨ (False ∨ p4)) := by
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- False on the left can always be used.
    apply False.elim h5
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h6 := h1 h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_342509762805708610768501820688 : (p2 → (((p5 ∨ (p3 → ((p4 ∧ (p5 ∨ p1)) → (p5 ∨ (p5 ∨ p5))))) → p1) → (((p3 → False) ∧ ((p2 ∨ p4) ∧ p2)) ∨ (p5 → True)))) := by
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
theorem thm_5_vars_225276147246195439334741527267 : (((True ∨ p4) ∧ p1) ∨ (((False ∧ ((p3 → p1) ∨ (p4 ∧ p4))) ∨ ((((p5 ∨ ((p2 ∨ p2) ∨ False)) ∧ p3) ∧ p1) ∨ True)) ∧ (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113230559147440030149867719761 : (((((((True ∨ p5) ∧ p2) ∧ (p3 ∧ True)) ∧ (p1 → (False ∨ (p4 ∧ (p5 ∧ (p5 ∨ (p5 ∧ True))))))) → p1) ∧ (p1 → p3)) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_193988041937461790643085351681 : ((p3 ∨ (False ∧ ((p3 → True) ∧ (False ∧ (p4 ∧ True))))) → ((True ∧ (p3 ∧ (p3 → (False ∧ (False ∧ False))))) ∨ ((p4 ∧ (True ∧ p5)) ∨ True))) := by
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
    -- False on the left can always be used.
    apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312064751143703311593532128513 : (p2 ∨ (p5 ∨ ((p2 ∨ ((p1 → ((p2 ∨ p2) → (((p1 → p3) ∧ p5) ∧ (p1 ∧ p3)))) ∧ (p4 ∧ p1))) ∨ (((p3 ∨ True) ∧ p5) → True)))) := by
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
theorem thm_5_vars_178126102951918486585931013338 : ((((p5 → (p3 → (p1 → (p2 → p5)))) ∨ ((p3 → p2) ∧ p3)) → p5) ∨ (((False → ((p1 ∨ p4) ∧ ((p5 ∧ p3) → p5))) ∨ p5) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152109185244980899769863021015 : (((((p5 ∨ ((p3 ∨ True) ∧ True)) ∨ p1) ∧ p3) ∧ ((p2 → (p5 → (p3 → ((p3 ∧ False) → p5)))) ∨ p4)) → ((p2 ∨ p1) ∨ (p1 → p1))) := by
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
    cases h6
    case inl h7 =>
      -- Disjunctions on the left can always be decomposed.
      cases h3
      case inl h8 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h9
        -- One of the premise coincides with the conclusion.
        exact h9
      case inr h10 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h11
        -- One of the premise coincides with the conclusion.
        exact h11
    case inr h12 =>
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h13
      case inl h15 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h16 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h17
          -- One of the premise coincides with the conclusion.
          exact h17
        case inr h18 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h19
          -- One of the premise coincides with the conclusion.
          exact h19
      case inr h20 =>
        -- Disjunctions on the left can always be decomposed.
        cases h3
        case inl h21 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h22
          -- One of the premise coincides with the conclusion.
          exact h22
        case inr h23 =>
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- Implications on the right can always be decomposed.
          intro h24
          -- One of the premise coincides with the conclusion.
          exact h24
  case inr h25 =>
    -- Disjunctions on the left can always be decomposed.
    cases h3
    case inl h26 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25
    case inr h27 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- One of the premise coincides with the conclusion.
      exact h25



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_186093810677907803313399086839 : ((((((p5 ∨ False) ∨ (p4 → False)) ∨ p3) ∧ (True ∧ p1)) ∨ p1) → (p5 ∨ ((((p1 ∨ (p1 ∧ p2)) → False) ∧ (p2 ∨ False)) → (False ∧ p4)))) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h4.left
          let h9 := h4.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h7
        case inr h10 =>
          -- False on the left can always be used.
          apply False.elim h10
      case inr h11 =>
        -- Conjunctions on the left can always be decomposed.
        let h12 := h4.left
        let h13 := h4.right
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h14
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- Conjunctions on the left can always be decomposed.
        let h15 := h14.left
        let h16 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h16
        case inl h17 =>
          -- We want to use the implication h15 based on <expert-advice>. So we show its premise.
          have h18 : (p1 ∨ (p1 ∧ p2)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h15, we can now drive its conclusion.
          let h19 := h15 h18
          -- False on the left can always be used.
          apply False.elim h19
        case inr h20 =>
          -- False on the left can always be used.
          apply False.elim h20
        -- Conjunctions on the left can always be decomposed.
        let h21 := h14.left
        let h22 := h14.right
        -- Disjunctions on the left can always be decomposed.
        cases h22
        case inl h23 =>
          -- We want to use the implication h21 based on <expert-advice>. So we show its premise.
          have h24 : (p1 ∨ (p1 ∧ p2)) := by
            -- Show the left disjunct based on <expert-advice>.
            apply Or.inl
            -- One of the premise coincides with the conclusion.
            exact h13
          -- We have shown the premise of h21, we can now drive its conclusion.
          let h25 := h21 h24
          -- False on the left can always be used.
          apply False.elim h25
        case inr h26 =>
          -- False on the left can always be used.
          apply False.elim h26
    case inr h27 =>
      -- Conjunctions on the left can always be decomposed.
      let h28 := h4.left
      let h29 := h4.right
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h30
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- Conjunctions on the left can always be decomposed.
      let h31 := h30.left
      let h32 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h32
      case inl h33 =>
        -- We want to use the implication h31 based on <expert-advice>. So we show its premise.
        have h34 : (p1 ∨ (p1 ∧ p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h31, we can now drive its conclusion.
        let h35 := h31 h34
        -- False on the left can always be used.
        apply False.elim h35
      case inr h36 =>
        -- False on the left can always be used.
        apply False.elim h36
      -- Conjunctions on the left can always be decomposed.
      let h37 := h30.left
      let h38 := h30.right
      -- Disjunctions on the left can always be decomposed.
      cases h38
      case inl h39 =>
        -- We want to use the implication h37 based on <expert-advice>. So we show its premise.
        have h40 : (p1 ∨ (p1 ∧ p2)) := by
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h29
        -- We have shown the premise of h37, we can now drive its conclusion.
        let h41 := h37 h40
        -- False on the left can always be used.
        apply False.elim h41
      case inr h42 =>
        -- False on the left can always be used.
        apply False.elim h42
  case inr h43 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h44
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the left can always be decomposed.
    let h45 := h44.left
    let h46 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h46
    case inl h47 =>
      -- We want to use the implication h45 based on <expert-advice>. So we show its premise.
      have h48 : (p1 ∨ (p1 ∧ p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h45, we can now drive its conclusion.
      let h49 := h45 h48
      -- False on the left can always be used.
      apply False.elim h49
    case inr h50 =>
      -- False on the left can always be used.
      apply False.elim h50
    -- Conjunctions on the left can always be decomposed.
    let h51 := h44.left
    let h52 := h44.right
    -- Disjunctions on the left can always be decomposed.
    cases h52
    case inl h53 =>
      -- We want to use the implication h51 based on <expert-advice>. So we show its premise.
      have h54 : (p1 ∨ (p1 ∧ p2)) := by
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h43
      -- We have shown the premise of h51, we can now drive its conclusion.
      let h55 := h51 h54
      -- False on the left can always be used.
      apply False.elim h55
    case inr h56 =>
      -- False on the left can always be used.
      apply False.elim h56



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_357364768289539706428010733304 : (p5 → ((True ∧ p2) → ((p2 → (((p2 → p1) ∨ p3) → (((((False ∨ p5) ∧ (p3 ∧ p2)) ∧ p4) ∨ (p2 → p2)) ∨ (p3 ∧ p4)))) ∨ p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h2.left
  let h4 := h2.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_187781810682789585636149231550 : ((p3 → (((p5 ∨ False) → (p1 ∨ ((p5 → p3) → False))) → p2)) → (((((p3 ∨ True) ∧ (False ∨ (p2 ∧ p1))) → False) ∧ False) ∨ (p2 → p2))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_135637598724812825529267417820 : (((((p4 ∧ p4) ∨ ((p5 → (False ∨ (p4 → True))) ∨ ((p5 ∧ p3) ∨ False))) → False) → (p4 ∧ ((p5 → False) ∨ True))) ∨ (p3 → (p2 ∨ p4))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p4 ∧ p4) ∨ ((p5 → (False ∨ (p4 → True))) ∨ ((p5 ∧ p3) ∨ False))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h4
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254682768378700138421885311249 : ((p3 ∧ p2) → (True → (p1 ∨ ((True ∧ ((((p1 ∧ (((True ∧ p5) ∨ True) ∧ (((True ∨ p2) ∨ False) ∧ False))) ∧ p2) ∨ p3) ∧ False)) ∨ p3)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the left can always be decomposed.
  let h3 := h1.left
  let h4 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_233385367075611080875214764621 : ((False ∨ (p4 ∧ p2)) → (((((p5 ∨ p1) ∧ (p3 → p3)) ∧ p3) ∨ (((((p1 → p3) ∧ False) ∧ (p5 ∨ p5)) ∨ (p1 ∧ p5)) ∨ p4)) ∨ p1)) := by
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
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_346772978971577094357071803425 : (p3 → ((((False ∧ False) ∨ (True ∧ (p1 ∨ (p5 → ((p3 ∨ (p5 ∧ p1)) ∨ ((p1 → p1) → p4)))))) → False) ∨ ((p3 → (p1 ∧ p2)) ∨ True))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_249414269504994128004642478432 : ((p5 ∨ False) ∨ ((p3 ∧ (p3 ∨ (((((p2 → True) ∨ p2) ∧ p3) ∧ p5) ∧ (((p5 ∧ p1) ∨ False) ∨ (p1 ∧ ((False → p3) → p4)))))) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_307231621265070032889486276004 : (p1 ∨ (p1 ∨ (p2 → (p1 → (p2 → ((p4 ∧ (((False ∧ False) ∧ (p5 ∨ p2)) ∨ ((p5 ∧ (True → (p1 → (p1 ∧ False)))) ∨ True))) ∨ p2)))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_699768757416147141141339805437 : ((((((p1 ∨ (p2 → (True ∧ (True → p3)))) → p2) ∨ (p2 → False)) → ((((p5 → (False ∧ p2)) ∧ p3) ∧ p4) ∨ (p5 → (True → p2)))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147190343505070277886064774155 : (((p4 ∨ ((p1 ∨ ((False ∨ p2) ∨ p5)) ∨ ((((p3 ∨ False) ∧ p4) ∧ ((p3 ∨ p1) ∨ p1)) → True))) ∧ p1) ∨ ((p4 → p1) ∨ (True → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_353936022427108230862849222794 : (p4 → (p2 → (p2 ∧ ((((p1 ∨ p4) ∧ ((((p1 ∨ p4) ∨ (p1 → ((True ∧ p1) → (p5 ∨ p3)))) ∧ p1) → False)) ∧ (p5 ∨ False)) ∨ p2)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_315392245757443171930283571726 : (p3 ∨ (((p3 ∨ False) ∧ p2) ∨ ((p1 → (p2 ∧ (((False ∨ p1) ∨ p3) ∧ False))) → (True ∧ (p4 → (((p2 ∧ True) ∨ p5) ∨ (p4 ∧ True))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- One of the premise coincides with the conclusion.
  exact h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_113495636237398710351887182457 : ((((((True ∧ (p4 → ((((p1 ∨ p1) ∧ p1) → True) ∨ p3))) → (p2 ∨ p4)) → False) ∨ (p3 ∨ (True → True))) ∨ (p2 → p1)) ∨ (p2 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_150163923244418462138539658253 : ((p1 → ((p2 ∨ ((True → p3) ∨ (p2 ∨ False))) ∨ ((p3 ∨ (((p1 ∧ p4) ∨ p2) ∨ p1)) → (p3 ∨ p4)))) ∨ (p3 → ((True ∨ p2) → p3))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- One of the premise coincides with the conclusion.
    exact h1
  case inr h4 =>
    -- One of the premise coincides with the conclusion.
    exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_748975349877845695480015727867 : ((((p4 → p4) → (((p4 → False) ∨ (((((True ∨ (p5 ∨ False)) ∧ (True ∧ p3)) → ((p4 → p1) ∨ p4)) ∧ (False ∨ p1)) ∨ p2)) ∨ True)) ∨ p5) ∧ True) := by
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
theorem thm_5_vars_53773290445487397066813407147 : (((((p1 → ((False ∧ p5) → (False ∨ p1))) → p1) ∨ p4) ∨ ((p4 ∨ (((p5 ∨ (p2 ∨ p3)) ∧ p3) ∨ ((True ∨ False) ∨ p2))) → True)) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_136249299303843118335728979445 : (((p2 ∨ ((True ∨ p5) ∧ (p3 ∧ p3))) ∨ (((p1 → p5) ∨ ((p2 ∧ (True → ((p2 ∧ False) ∧ True))) ∨ p2)) → p5)) ∨ ((False ∧ p4) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_337358375206117337476163851111 : (p1 → ((((((p3 ∧ ((((False → p2) → p1) ∨ ((p1 → p1) ∧ False)) ∧ p3)) ∧ p1) → True) ∧ True) → (p4 ∧ p1)) ∨ (p1 ∨ (p2 ∧ p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111199389440455682241383691244 : ((((p1 → (True → p1)) ∧ (((p1 → ((p1 ∧ p5) ∧ ((p4 ∧ False) → (p1 ∧ (p5 → False))))) → (False ∨ False)) ∧ True)) ∧ p2) ∨ (True ∨ p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



