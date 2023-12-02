variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_241575960869492078816472470915 : ((False → p4) ∧ ((((((True ∧ p2) ∨ (p1 ∧ (p4 ∧ (p5 → (p2 ∧ p1))))) → p3) ∧ (p1 → (((p2 ∨ False) → p5) ∨ False))) ∧ p3) ∨ True)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_773545378889051949258986734981 : (((False ∨ (((p1 ∧ (p3 ∨ ((p5 ∨ (p1 → (p1 ∨ p2))) → p5))) → ((p3 ∨ p5) ∨ (((p1 ∨ (p1 ∧ p5)) ∨ p2) ∧ p3))) ∨ True)) ∨ p2) ∧ True) := by
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
theorem thm_5_vars_135835701623412733083073145955 : ((((False ∨ p5) ∧ ((p1 ∧ p3) ∨ ((False ∨ p2) ∨ (p5 ∨ True)))) ∧ ((True ∨ (((p1 ∨ True) → True) → True)) ∧ False)) ∨ ((p4 ∧ p5) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_389812674305464905906305486074 : (((((False ∧ (False ∨ (((p2 ∧ p4) ∨ (p5 → (p1 → p2))) ∧ p5))) ∨ (True ∨ (False ∧ (p5 ∧ (p3 → (p1 → (p2 ∨ p4))))))) ∨ p2) ∧ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44076343721801553703974005538 : ((((((p3 ∨ ((False ∨ (p5 ∧ p3)) ∧ p3)) ∨ (p3 → p3)) → (True → ((False ∨ (p4 → p5)) ∧ False))) ∧ ((True → False) → p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312959456696021409537930148825 : (p3 ∨ (((((((p5 → False) ∨ p4) ∨ ((p2 → p5) ∧ p4)) ∧ ((((p4 ∧ p1) ∨ False) ∧ (p1 ∨ p3)) ∨ (p3 ∨ p1))) → p1) ∧ True) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_255982549825901164428587648654 : ((True ∨ p3) → (((p3 ∨ p1) ∨ ((((p3 ∧ p4) ∧ ((p4 ∧ p5) ∨ (((False ∨ p2) ∧ p5) ∧ True))) ∨ False) ∨ (False → False))) ∨ (p1 ∨ p3))) := by
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
    -- Implications on the right can always be decomposed.
    intro h3
    -- False on the left can always be used.
    apply False.elim h3
  case inr h4 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_116991662264292335609331568851 : (((True ∨ False) → ((p5 ∨ False) ∨ (((p5 ∨ ((((p1 ∨ False) ∧ True) ∧ (((True ∧ p4) ∧ p4) → False)) → False)) ∨ p4) ∧ False))) ∨ (p3 ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_117595274478284775501672051189 : ((p2 ∧ (False ∨ (((True ∧ ((p5 ∧ p2) → p2)) → (True → (p3 ∨ (((p3 → True) ∧ p1) ∧ (p5 ∨ (p2 ∨ p4)))))) ∧ p5))) ∨ (False → p4)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_172126506999473151793145578688 : ((((((False ∨ (p5 → p5)) ∨ p1) ∧ p1) → (p5 ∧ False)) ∧ (False → (p2 ∧ p2))) ∨ (((p3 → False) ∧ p4) → (p1 ∨ ((p1 ∧ p4) → True)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_690043326023455111220747436405 : ((((p4 ∧ (((p2 → (p3 → p2)) → (False ∨ ((p4 → (True ∧ p4)) → p1))) ∧ False)) ∨ (((p1 ∨ (p1 → p5)) → p2) ∨ (True ∨ p5))) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139858285430451625637894500973 : (((((((((p4 ∨ p1) ∧ (p5 → p4)) ∧ ((p5 ∨ p2) ∨ p3)) → (p5 ∧ p3)) ∧ p5) ∧ p4) ∧ True) ∧ (p4 ∧ p2)) → ((False ∨ p3) ∨ p3)) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h8 := h6.left
  let h9 := h6.right
  -- Conjunctions on the left can always be decomposed.
  let h10 := h3.left
  let h11 := h3.right
  -- We want to use the implication h8 based on <expert-advice>. So we show its premise.
  have h12 : (((p4 ∨ p1) ∧ (p5 → p4)) ∧ ((p5 ∨ p2) ∨ p3)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Implications on the right can always be decomposed.
    intro h13
    -- One of the premise coincides with the conclusion.
    exact h10
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- One of the premise coincides with the conclusion.
    exact h9
  -- We have shown the premise of h8, we can now drive its conclusion.
  let h14 := h8 h12
  -- We need to get the right conjuct of h14 based on <expert-advice>.
  let h15 := h14.right
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h15



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_80066624756627326775263049614 : (((((((True → ((p3 ∧ True) → False)) ∧ (p4 ∨ (True ∧ ((p3 ∨ (p3 ∨ (p1 ∨ p2))) ∨ True)))) → p5) ∧ False) ∨ True) → (p1 ∧ False)) → p2) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True → ((p3 ∧ True) → False)) ∧ (p4 ∨ (True ∧ ((p3 ∨ (p3 ∨ (p1 ∨ p2))) ∨ True)))) → p5) ∧ False) ∨ True) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_349226066800764806692920193179 : (p3 → (p1 → (((((True ∧ (False ∨ p1)) ∧ (((p3 ∧ (True → (((False ∧ p1) ∧ p5) ∧ False))) ∧ False) → p3)) ∨ False) ∨ p3) → (p5 → p5)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Implications on the right can always be decomposed.
  intro h4
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
      let h9 := h7.left
      let h10 := h7.right
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- False on the left can always be used.
        apply False.elim h11
      case inr h12 =>
        -- One of the premise coincides with the conclusion.
        exact h4
    case inr h13 =>
      -- False on the left can always be used.
      apply False.elim h13
  case inr h14 =>
    -- One of the premise coincides with the conclusion.
    exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_134063935166054802586473135516 : (((((False → (p1 → ((p3 ∨ (((p2 ∧ (p5 ∧ (p4 → p4))) ∧ p5) → True)) ∨ (p1 ∨ p5)))) ∧ True) → p4) ∨ True) ∨ ((p5 ∧ False) → False)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_314103548177356992306295522704 : (p3 ∨ ((((True ∧ (p4 ∨ True)) → p5) ∧ (p4 ∨ (((p4 ∨ ((p2 ∧ p3) → (True ∨ True))) ∨ (p3 ∧ True)) ∧ (p4 → p5)))) → (p5 ∨ False))) := by
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
    -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
    have h5 : (True ∧ (p4 ∨ True)) := by
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h4
    -- We have shown the premise of h2, we can now drive its conclusion.
    let h6 := h2 h5
    -- One of the premise coincides with the conclusion.
    exact h6
  case inr h7 =>
    -- Conjunctions on the left can always be decomposed.
    let h8 := h7.left
    let h9 := h7.right
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h10 =>
      -- Disjunctions on the left can always be decomposed.
      cases h10
      case inl h11 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h9 based on <expert-advice>. So we show its premise.
        have h12 : p4 := by
          -- One of the premise coincides with the conclusion.
          exact h11
        -- We have shown the premise of h9, we can now drive its conclusion.
        let h13 := h9 h12
        -- One of the premise coincides with the conclusion.
        exact h13
      case inr h14 =>
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
        have h15 : (True ∧ (p4 ∨ True)) := by
          -- Conjunctions on the right can always be decomposed.
          apply And.intro
          -- True on the right can always be proven directly.
          apply True.intro
          -- Show the right disjunct based on <expert-advice>.
          apply Or.inr
          -- True on the right can always be proven directly.
          apply True.intro
        -- We have shown the premise of h2, we can now drive its conclusion.
        let h16 := h2 h15
        -- One of the premise coincides with the conclusion.
        exact h16
    case inr h17 =>
      -- Conjunctions on the left can always be decomposed.
      let h18 := h17.left
      let h19 := h17.right
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- We want to use the implication h2 based on <expert-advice>. So we show its premise.
      have h20 : (True ∧ (p4 ∨ True)) := by
        -- Conjunctions on the right can always be decomposed.
        apply And.intro
        -- True on the right can always be proven directly.
        apply True.intro
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h2, we can now drive its conclusion.
      let h21 := h2 h20
      -- One of the premise coincides with the conclusion.
      exact h21



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_216777971687129606337629874528 : (((True ∧ (p5 ∨ p3)) ∧ p3) → ((p4 ∧ p2) ∨ ((p4 ∧ ((p4 ∨ (True ∨ (p5 ∧ ((False → p3) → ((p5 ∧ True) ∨ p4))))) → True)) ∨ True))) := by
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_709339848842544207848760431707 : (((((p2 → True) → (p5 ∧ ((p3 ∧ False) → p1))) → (((True ∨ (p3 ∨ p1)) → (True ∧ p5)) ∧ ((p5 → (p1 → True)) → (p1 ∨ p5)))) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h3 =>
    -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
    have h4 : (p2 → True) := by
      -- Implications on the right can always be decomposed.
      intro h5
      -- True on the right can always be proven directly.
      apply True.intro
    -- We have shown the premise of h1, we can now drive its conclusion.
    let h6 := h1 h4
    -- We need to get the left conjuct of h6 based on <expert-advice>.
    let h7 := h6.left
    -- One of the premise coincides with the conclusion.
    exact h7
  case inr h8 =>
    -- Disjunctions on the left can always be decomposed.
    cases h8
    case inl h9 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h10 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h11
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h12 := h1 h10
      -- We need to get the left conjuct of h12 based on <expert-advice>.
      let h13 := h12.left
      -- One of the premise coincides with the conclusion.
      exact h13
    case inr h14 =>
      -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
      have h15 : (p2 → True) := by
        -- Implications on the right can always be decomposed.
        intro h16
        -- True on the right can always be proven directly.
        apply True.intro
      -- We have shown the premise of h1, we can now drive its conclusion.
      let h17 := h1 h15
      -- We need to get the left conjuct of h17 based on <expert-advice>.
      let h18 := h17.left
      -- One of the premise coincides with the conclusion.
      exact h18
  -- Implications on the right can always be decomposed.
  intro h19
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h20 : (p2 → True) := by
    -- Implications on the right can always be decomposed.
    intro h21
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h22 := h1 h20
  -- We need to get the left conjuct of h22 based on <expert-advice>.
  let h23 := h22.left
  -- One of the premise coincides with the conclusion.
  exact h23
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_90139528574502610213290661070 : (((True ∧ (p3 → True)) → ((p1 ∧ (False ∨ (False → (((p3 ∧ p3) ∨ p5) → ((False → False) ∨ ((p5 ∨ p2) → (p2 ∨ False))))))) ∧ p3)) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (True ∧ (p3 → True)) := by
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h4 := h1 h2
  -- We need to get the right conjuct of h4 based on <expert-advice>.
  let h5 := h4.right
  -- One of the premise coincides with the conclusion.
  exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_260500890904545845079711377190 : ((p3 → False) → ((p5 → p5) → (((p2 → p5) ∨ (p5 ∨ p2)) → (((True ∧ p3) ∨ (((p3 ∨ (p1 ∧ p3)) ∨ True) ∨ (p2 → False))) ∨ p4)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
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
  case inr h5 =>
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
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
    case inr h7 =>
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
theorem thm_5_vars_219869439281717292972216929176 : ((p3 → (False → (False ∧ True))) → ((p4 ∧ (((p4 ∨ (p5 ∨ ((False ∧ (p5 ∧ p4)) → p3))) ∧ (p2 → (p5 ∨ (p3 ∧ True)))) ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111094560975942951868875378461 : ((((((False ∧ p1) ∨ (((True ∨ True) → p5) → (False ∧ p2))) → p3) → (p2 ∨ ((p1 ∨ (p2 → p1)) ∨ (p3 ∧ False)))) ∧ False) ∨ (True ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147332991258177181242013367886 : (((((p4 → ((p4 ∧ ((((True ∨ False) → True) ∧ False) ∨ (p2 ∨ p4))) ∧ p5)) → p1) ∨ (p2 → p4)) ∨ p3) ∨ (p2 ∨ ((True → False) → p4))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
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
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_152799328725850087007078616687 : (((p5 ∧ p3) → (((True → p3) ∨ True) ∨ ((((((p5 → p1) → p2) ∨ p4) ∧ p1) → (p4 → p5)) ∨ p3))) → ((p5 ∨ True) ∧ (p2 → p2))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_61767809862755127517999832541 : ((p2 ∧ ((((((((True ∨ False) → p5) → p3) ∧ p5) ∧ (p5 ∧ (p3 → False))) ∧ ((p3 ∨ True) ∧ (p2 ∨ p1))) ∨ (p5 ∨ True)) ∧ p3)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_651291427847302026534940085924 : (((((p4 ∨ (p4 ∧ p4)) ∧ (((((p4 ∧ ((p1 → p4) ∨ p3)) → p3) ∧ (p2 → p1)) ∨ (p4 ∨ (True ∧ True))) ∨ p2)) ∧ (p1 ∧ p4)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56139587409317857130424111512 : ((((True ∨ p2) → (p3 ∧ p4)) ∨ ((((((p2 → (p2 ∨ True)) ∧ True) → ((p3 ∧ p5) ∨ (p3 ∨ p3))) ∨ p3) ∧ p5) ∨ (False → False))) ∨ p5) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_166092960395246944377287388785 : (((True → p2) → (((True ∨ ((False ∧ True) ∨ False)) → p3) ∨ ((p4 → (False ∨ p1)) ∧ False))) ∨ (p4 ∨ ((p4 → p2) → ((True ∧ p1) → p1)))) := by
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_358522383513282953458929603495 : (p5 → (p2 → ((True ∧ (((p1 → ((False ∧ ((p4 ∨ p2) ∧ (p5 ∨ (p3 → (p1 → False))))) ∨ p4)) ∧ ((p3 ∨ p2) ∨ False)) ∨ p2)) ∨ p4))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_52992946987732195669540850136 : (((((p5 ∨ p4) ∧ ((p2 ∧ (False → p4)) ∨ p4)) ∨ (p1 ∨ False)) ∧ ((((p2 ∧ (p5 ∨ p5)) ∨ ((p4 → True) → p5)) → p3) ∨ True)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_42400959937041706853030407649 : (((p4 ∧ (p1 ∨ (((p1 ∨ (p2 → (False ∨ ((p5 → p5) ∧ p4)))) → p3) ∨ (True ∧ (((p5 → (p4 ∨ p5)) ∨ p5) ∧ p5))))) ∨ p3) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_338815355294593090718876942356 : (p1 → ((p3 ∨ False) ∨ (p1 → (p4 → (False ∨ ((((p3 ∧ True) ∨ p5) ∨ False) ∨ ((p3 → (p3 ∧ p4)) → (p1 ∨ ((True → False) ∧ p2))))))))) := by
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
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654697439441263306313161078436 : (((((((False → (p1 → ((((p3 ∨ (False ∧ (True → p2))) ∧ p2) → (p2 ∨ False)) ∨ (p4 ∧ p4)))) ∧ p5) ∨ p5) → False) ∨ (True ∧ True)) ∨ p3) ∧ True) := by
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_586250788372392592573631784914 : (((((((p5 ∨ p3) ∧ ((False → (p4 ∧ (p5 → p3))) → p2)) ∨ (((True → True) ∧ (((True → p1) → True) → p4)) ∨ p1)) ∧ p1) ∧ True) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_350151256399373919922834836650 : (p4 → ((((((False → p1) → (p1 → p5)) ∧ False) ∨ (p3 ∨ p1)) ∨ (False → (((p2 ∨ ((p1 ∨ False) ∧ p1)) → p3) ∧ (p2 ∧ False)))) ∨ p5)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h2
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h3
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h2
  case inr h5 =>
    -- Conjunctions on the left can always be decomposed.
    let h6 := h5.left
    let h7 := h5.right
    -- Disjunctions on the left can always be decomposed.
    cases h6
    case inl h8 =>
      -- False on the left can always be used.
      apply False.elim h2
    case inr h9 =>
      -- False on the left can always be used.
      apply False.elim h9
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_56260410668584643638295103265 : (((p2 → ((p2 → p2) ∧ p3)) ∨ (((((p4 → p3) ∨ p2) ∨ (p1 → (p2 ∨ False))) → ((p4 → True) → (False ∨ p3))) ∨ (False → p1))) ∨ p3) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_37915890815249584083433906321 : ((((((True → p2) → (False → p3)) ∧ (p2 ∨ ((((p2 ∧ (p3 → False)) → (p1 → True)) → (p3 ∧ p3)) → False))) ∧ (p4 ∧ False)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_218201397044870709550482848047 : (((p2 ∧ p4) ∨ (p5 ∨ True)) → ((((p4 ∧ False) ∨ (True ∨ p4)) ∧ ((((p1 → ((p5 ∨ True) → (p2 ∨ p3))) → False) ∨ p4) ∧ False)) ∨ True)) := by
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
theorem thm_5_vars_233765330487008513559341596766 : ((p3 ∨ (p2 ∨ True)) → (((p5 ∧ (p4 ∨ (p4 → (False → True)))) → (True ∧ (((p2 ∧ True) ∧ p1) ∨ (p3 → ((p4 ∨ True) ∨ p1))))) ∨ p4)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h2 =>
    -- Show the left disjunct based on <expert-advice>.
    apply Or.inl
    -- Implications on the right can always be decomposed.
    intro h3
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Conjunctions on the left can always be decomposed.
    let h4 := h3.left
    let h5 := h3.right
    -- Disjunctions on the left can always be decomposed.
    cases h5
    case inl h6 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h7
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- One of the premise coincides with the conclusion.
      exact h6
    case inr h8 =>
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- Implications on the right can always be decomposed.
      intro h9
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Show the right disjunct based on <expert-advice>.
      apply Or.inr
      -- True on the right can always be proven directly.
      apply True.intro
  case inr h10 =>
    -- Disjunctions on the left can always be decomposed.
    cases h10
    case inl h11 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h12
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h13 := h12.left
      let h14 := h12.right
      -- Disjunctions on the left can always be decomposed.
      cases h14
      case inl h15 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h16
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h15
      case inr h17 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h18
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro
    case inr h19 =>
      -- Show the left disjunct based on <expert-advice>.
      apply Or.inl
      -- Implications on the right can always be decomposed.
      intro h20
      -- Conjunctions on the right can always be decomposed.
      apply And.intro
      -- True on the right can always be proven directly.
      apply True.intro
      -- Conjunctions on the left can always be decomposed.
      let h21 := h20.left
      let h22 := h20.right
      -- Disjunctions on the left can always be decomposed.
      cases h22
      case inl h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h24
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- One of the premise coincides with the conclusion.
        exact h23
      case inr h25 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- Implications on the right can always be decomposed.
        intro h26
        -- Show the left disjunct based on <expert-advice>.
        apply Or.inl
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49521070019634304568123899469 : ((((False → ((((False → (False → (p2 → (p4 ∧ p4)))) ∧ p1) ∨ (p4 ∧ p1)) ∧ (p1 → p3))) ∧ (True ∨ p1)) → (True → (p1 ∧ p1))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49968084887764471157787239849 : ((((((p2 ∧ ((((p3 → True) ∧ False) ∨ (p2 ∧ p2)) ∨ p4)) ∨ p3) ∨ p4) ∨ ((p2 ∧ p3) → p3)) ∧ (((p2 → p3) → p4) ∨ True)) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_59989482064639209185291049601 : (((False ∨ p2) → (p2 ∧ (True ∧ ((((((p2 ∨ p3) ∨ p4) ∧ p2) → (p2 → (p3 ∨ p1))) ∨ (p4 ∨ p4)) ∨ (p4 → (p1 → p2)))))) ∨ p4) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
    -- One of the premise coincides with the conclusion.
    exact h3
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Disjunctions on the left can always be decomposed.
  cases h1
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
  case inr h5 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Implications on the right can always be decomposed.
    intro h6
    -- Implications on the right can always be decomposed.
    intro h7
    -- One of the premise coincides with the conclusion.
    exact h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_197373279435649694914651284716 : (((False ∨ (((False ∧ p1) ∨ p5) → p4)) → p1) ∨ ((p1 ∨ False) ∨ (p3 ∨ ((False ∧ (p4 ∧ ((((p4 ∧ p4) ∧ p2) ∧ p3) ∨ p1))) → True)))) := by
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
theorem thm_5_vars_218628047531504294784790078263 : ((True ∧ ((p2 ∨ p4) ∧ p3)) → ((p5 ∨ (p1 ∨ ((p4 ∨ ((p5 ∨ False) → p3)) → (p5 ∧ (((p2 → False) ∧ p5) → (p1 ∨ p1)))))) ∨ True)) := by
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
theorem thm_5_vars_323681743404941975624915326963 : (p5 ∨ ((p2 ∧ (p1 ∨ (p4 ∧ ((p1 ∨ (p2 ∨ (((p5 ∧ p5) ∨ p2) → (True ∨ (False → p4))))) → False)))) ∨ ((False ∧ p1) → (p4 ∧ False)))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111625228960318630261892834504 : (((((p1 ∨ (p3 ∧ ((False → False) ∧ ((((False ∨ (True ∨ (p5 ∨ p1))) ∧ p5) ∨ p4) ∧ p3)))) ∨ (p2 → p1)) ∨ p5) ∨ True) ∨ (p1 ∨ p3)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_62520544715475445185383722912 : ((p3 ∧ (p4 ∧ (p4 ∨ (((p3 ∨ p3) ∧ (((False ∧ p3) ∨ p5) ∨ p1)) ∨ (((((p2 ∨ p5) ∨ p4) → p2) → p4) ∨ (p3 ∧ p4)))))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_736863202335116982568632323624 : ((((p2 → p4) ∧ ((p1 ∨ (((False ∨ (p5 ∧ (p5 → False))) ∧ (p4 → p1)) ∨ (p1 ∨ False))) ∧ (False ∧ (p4 ∧ (p3 ∨ (p4 ∨ p3)))))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65213709761159432016810578074 : ((p3 ∨ (((p1 ∧ (p1 → (p5 → ((p4 ∧ (True ∨ ((True ∧ True) → p4))) ∧ p5)))) → (((p5 ∨ p4) ∧ (True → p5)) → p5)) ∨ False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_127472107008462905734286150959 : ((p3 ∨ (p3 ∨ (((p4 ∧ p5) ∨ (True ∨ (((False ∨ (((True → True) ∨ p2) → False)) ∧ (p4 ∧ p5)) ∨ (p1 ∨ True)))) ∨ p3))) → (p4 ∨ True)) := by
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
        -- Disjunctions on the left can always be decomposed.
        cases h6
        case inl h7 =>
          -- Conjunctions on the left can always be decomposed.
          let h8 := h7.left
          let h9 := h7.right
          -- Show the left disjunct based on <expert-advice>.
          apply Or.inl
          -- One of the premise coincides with the conclusion.
          exact h8
        case inr h10 =>
          -- Disjunctions on the left can always be decomposed.
          cases h10
          case inl h11 =>
            -- Show the right disjunct based on <expert-advice>.
            apply Or.inr
            -- True on the right can always be proven directly.
            apply True.intro
          case inr h12 =>
            -- Disjunctions on the left can always be decomposed.
            cases h12
            case inl h13 =>
              -- Conjunctions on the left can always be decomposed.
              let h14 := h13.left
              let h15 := h13.right
              -- Disjunctions on the left can always be decomposed.
              cases h14
              case inl h16 =>
                -- False on the left can always be used.
                apply False.elim h16
              case inr h17 =>
                -- Conjunctions on the left can always be decomposed.
                let h18 := h15.left
                let h19 := h15.right
                -- Show the left disjunct based on <expert-advice>.
                apply Or.inl
                -- One of the premise coincides with the conclusion.
                exact h18
            case inr h20 =>
              -- Disjunctions on the left can always be decomposed.
              cases h20
              case inl h21 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
              case inr h22 =>
                -- Show the right disjunct based on <expert-advice>.
                apply Or.inr
                -- True on the right can always be proven directly.
                apply True.intro
      case inr h23 =>
        -- Show the right disjunct based on <expert-advice>.
        apply Or.inr
        -- True on the right can always be proven directly.
        apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_587154990103795031760331859621 : (((((p3 → (True ∧ ((p3 ∧ (((p5 ∧ p4) → ((p5 ∧ p2) ∨ (((False ∨ p5) ∧ p4) → False))) → (p5 → p2))) ∧ p5))) ∧ p3) ∧ p3) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_312980764126264643510787685384 : (p3 ∨ (((p3 ∧ ((((p4 ∨ True) ∨ (p2 ∨ (((p5 ∨ (True → (p5 ∨ p3))) ∨ False) ∨ p2))) ∧ (p2 ∨ (p5 ∧ p3))) ∨ True)) ∧ p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_158157561322377078327437082517 : (((p3 → ((False ∧ True) ∧ False)) ∨ ((((p3 ∨ (p2 → p1)) ∧ p3) ∧ ((True ∨ p4) → p2)) ∨ True)) ∨ (((p1 → p3) ∨ True) ∨ (False → p5))) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_54437112060430452640010672956 : ((((p2 ∨ (p4 ∧ ((p4 → p3) → p4))) ∨ p4) ∨ ((p1 → (p4 ∨ False)) ∨ (p2 ∧ ((p4 → ((p2 ∨ (True → p2)) → True)) ∨ p3)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_148611561088279835743571730694 : ((((p3 ∧ ((p2 ∨ p5) ∧ (p2 ∧ (p3 ∧ p1)))) ∨ p1) → ((((p2 → False) ∨ (p2 → p5)) → False) ∨ p3)) ∨ (True ∧ ((False → p3) ∨ p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_622659723032573907139905538442 : ((((p4 ∧ ((p1 → ((p4 ∧ p3) → (((False → False) ∧ ((p3 ∨ True) ∨ p1)) ∨ True))) ∧ (((p1 ∧ p5) ∧ True) ∨ (p5 ∧ p5)))) ∨ False) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_149035599834860819249274213245 : (((p3 ∧ (True ∨ p4)) ∨ (p2 → (((p4 ∧ (False ∧ p3)) → p3) → (p2 → ((True → False) ∨ (p3 ∧ False)))))) ∨ (True → ((p4 ∧ False) → p3))) := by
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
  apply False.elim h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_50359452337560218689096043409 : (((((p1 ∧ p1) ∧ True) ∧ (((True ∧ True) → ((p3 ∧ False) ∧ False)) ∨ ((True → (p3 ∧ p4)) ∧ p1))) ∨ (p3 → ((p3 ∨ p2) ∨ p5))) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- One of the premise coincides with the conclusion.
  exact h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_66534361411409029412159633860 : ((True → ((((True ∧ p1) ∨ p3) ∨ ((p4 ∨ ((p1 ∨ (p5 ∧ p2)) → (((p3 ∨ p3) → ((p2 ∧ True) ∧ p3)) ∧ p4))) → True)) → p2)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_264980888442863027667875742833 : (True ∧ ((True → False) → (((p1 ∧ ((((p1 ∧ p2) ∨ p5) ∧ p5) → (((p5 ∨ (p2 ∧ p1)) ∧ (p3 ∨ p2)) → (p5 ∧ True)))) → p3) ∨ p5))) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : True := by
    -- True on the right can always be proven directly.
    apply True.intro
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h3 := h1 h2
  -- False on the left can always be used.
  apply False.elim h3



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_46241507391709524590710559149 : (((((p2 ∧ p2) → ((p5 ∨ (((p3 → True) ∨ p3) → (((p3 → (p3 ∧ p1)) ∨ False) ∧ True))) ∨ p2)) ∨ (p5 ∨ p2)) ∧ (p3 → True)) ∨ p2) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- Implications on the right can always be decomposed.
  intro h4
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48542383929802039962158703929 : ((((((((p5 ∨ p5) ∧ False) ∧ (False → True)) → (((p3 ∧ (p5 ∧ True)) ∨ True) ∨ (p3 ∧ p1))) ∧ p5) → p1) ∧ ((False → p2) → False)) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_48566236764478079185496657140 : (((((p1 → (p1 ∧ True)) ∧ ((p4 ∧ (True ∧ (True ∨ ((True → (p1 ∨ (p4 → True))) → p3)))) → p1)) → p4) ∧ (False → (p4 ∨ True))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_595109692292648614695474305305 : (((((((p2 ∨ ((p1 ∧ (True → p5)) ∧ p4)) ∧ ((p3 ∧ True) ∨ p4)) ∧ p5) → (p3 → ((((p1 ∨ p2) ∨ False) ∧ p1) ∨ p2))) ∧ p2) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_164922982549576191715592172122 : ((((((False → (p5 ∨ False)) ∨ (True ∧ (p2 → (p2 ∨ (p1 ∧ p5))))) → p2) ∨ p2) → False) ∨ (((p3 → ((False ∨ p4) → True)) ∧ False) → p4)) := by
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
theorem thm_5_vars_716201534048238057697085325796 : (((((False ∨ (p4 ∨ False)) → True) ∧ (((p3 ∨ (p2 → p1)) ∧ (((((p1 → ((p1 → p4) ∨ p1)) → p5) → p1) ∧ p4) ∨ p5)) ∨ True)) ∨ p5) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_205975487055744008112611934877 : ((p1 ∧ (((p4 → True) ∨ p2) → p1)) ∨ ((p4 → (p5 ∧ ((((p1 ∨ False) → p5) → (p1 ∨ (p5 → p2))) → (p4 ∨ p1)))) → (p1 → p1))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_792304782180777961905060345038 : (((True → ((((False ∨ (False ∨ p2)) → True) ∧ (((p5 ∨ p2) ∧ ((p4 ∨ p1) ∨ p4)) ∧ p4)) ∨ (False → (p1 ∧ ((True ∨ p3) ∨ False))))) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
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
  -- False on the left can always be used.
  apply False.elim h2
  -- False on the left can always be used.
  apply False.elim h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_308612126557779575293789467679 : (p2 ∨ (((p5 → p5) ∧ ((p1 ∨ (((((False → ((((p1 ∨ p3) ∨ p5) → p5) → p5)) ∧ (p5 ∨ p2)) ∧ p3) → p4) ∧ p2)) ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_745707530678896872648237331292 : ((((True ∨ p5) → (((((p3 ∧ p4) ∧ ((p1 ∨ True) ∨ (p2 ∧ True))) ∧ p5) ∧ (((True ∨ (True ∧ p1)) ∨ (p2 ∨ p1)) → p5)) ∨ True)) ∨ p3) ∧ True) := by
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
    -- True on the right can always be proven directly.
    apply True.intro
  case inr h3 =>
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- True on the right can always be proven directly.
    apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_178805363868928796146734665137 : ((((p2 ∨ True) → False) ∨ (p5 → ((p3 ∧ (False ∧ (p2 → False))) ∨ False))) ∨ ((True → (p1 ∨ (((True ∧ p4) → (p5 → True)) ∨ p3))) ∨ p2)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_711414685985328110738341770752 : ((((p3 ∨ ((p4 ∧ p1) ∧ (p3 ∧ True))) ∧ (p4 → ((p2 ∧ ((((p4 → (p5 → (p5 ∨ (p4 ∧ True)))) ∧ p3) ∨ p3) → p5)) ∨ p2))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_49166447793600013207775571976 : (((((p2 ∨ p1) ∧ ((p2 → False) ∨ False)) ∨ ((p5 → p5) → ((p3 ∧ p3) ∨ (((p5 → p2) → p5) ∨ p3)))) ∨ (True ∨ (p2 ∨ p5))) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_65994635908139511999328152705 : ((p4 ∨ (p3 → (True → ((((True ∨ (p5 ∧ (p5 ∧ (p4 → (p5 ∧ p5))))) → ((False ∧ p2) ∨ True)) ∨ (p5 ∧ (True ∨ p4))) → p4)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_133855777089804521041473206184 : (((p1 ∧ (((((p3 → False) ∨ True) ∧ (((((False ∧ (p2 → p5)) ∧ p5) → p3) → p1) ∧ True)) ∨ p2) → False)) ∧ False) ∨ ((True ∨ False) → True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_137444861525169213728930129445 : ((p4 ∧ ((((p1 ∧ False) ∨ p3) ∨ (p5 → (p3 → p4))) ∧ (p3 → ((p3 ∧ False) ∧ ((p1 ∧ (p3 ∧ False)) ∧ False))))) ∨ (p1 → (True ∨ False))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_38094283777600522109928005506 : ((((p3 ∨ ((p2 ∨ False) ∨ (p3 → ((False ∧ p2) ∨ ((False ∧ (False ∧ (p5 ∨ p1))) ∨ (p5 → (p2 → p3))))))) → (p2 ∧ p2)) ∧ p2) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_354682520072950039608878279123 : (p5 → (((((p1 → p4) → p1) ∨ (True → (False ∧ ((((((True ∨ p2) ∧ p4) ∨ p5) ∨ (p2 ∧ p5)) → p4) → p2)))) ∧ (p3 ∨ p4)) ∨ True)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_668695490282405530791057695379 : ((((((((p1 ∧ (p5 → True)) ∨ p1) ∧ (((p4 ∨ True) → (True ∧ ((p4 ∨ p5) → True))) → p5)) ∧ p4) ∨ p2) ∨ ((True → p3) → p3)) ∨ False) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
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
  -- One of the premise coincides with the conclusion.
  exact h3
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_299198970598666807909339692726 : (False ∨ (((p5 → ((p2 ∧ ((p5 ∧ p2) ∧ True)) ∧ (p1 ∧ ((p2 → (p2 ∨ False)) → (((p2 ∨ p1) → (p1 → p4)) ∨ p5))))) → p1) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44018092936389871402986660997 : (((((p3 ∧ ((p1 ∨ (p2 → p1)) ∨ (True ∨ p3))) ∨ ((p4 → ((p5 ∨ p4) ∨ (p4 ∧ p3))) ∨ (p1 ∨ True))) → (p5 ∧ p1)) → p1) ∨ p1) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : ((p3 ∧ ((p1 ∨ (p2 → p1)) ∨ (True ∨ p3))) ∨ ((p4 → ((p5 ∨ p4) ∨ (p4 ∧ p3))) ∨ (p1 ∨ True))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
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
  -- One of the premise coincides with the conclusion.
  exact h4



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_654478235929414509505782483034 : ((((((p3 ∧ p4) → (True ∧ (((p3 ∨ (True → False)) ∧ ((True ∨ False) ∨ ((True ∧ (p1 → p2)) ∧ p3))) → p1))) ∨ p1) ∨ (True ∨ p5)) ∨ p1) ∧ True) := by
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
theorem thm_5_vars_257629450374787361838377009469 : ((p3 ∨ p2) → ((((p2 ∧ ((p2 ∨ False) ∧ p3)) ∧ ((False ∧ (True → p1)) ∨ (True → p2))) ∧ p5) ∨ (True ∨ (p5 ∧ ((p2 ∧ p5) ∨ p1))))) := by
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
theorem thm_5_vars_694594218378878731846771456681 : ((((p4 ∧ (((True ∧ ((True ∨ False) ∧ False)) ∨ ((p2 ∧ False) → True)) ∧ p1)) ∨ ((True ∧ p2) → (((False ∧ (p3 ∧ p5)) ∧ p3) ∨ p3))) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_60157445415041536478624161272 : (((p4 ∨ p4) → ((p2 → (p4 → p5)) → (p3 ∧ (((((p2 → p3) ∧ p3) ∨ (((p4 ∧ (False ∨ True)) ∧ p4) → p1)) ∨ True) → p1)))) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_115513742797505578917462531718 : ((((p4 ∧ (p2 → p4)) ∧ ((p2 → True) ∨ p5)) → ((p2 ∨ p5) ∨ (((((p4 ∧ p5) ∨ p2) ∨ p3) ∧ (False → p5)) ∨ p1))) ∨ (False → p5)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_767206438228562571875462372735 : (((p5 ∧ (((((((True ∨ p5) ∧ p4) ∨ ((p3 ∨ ((((False ∧ True) ∧ True) → p3) ∧ (p1 ∧ True))) ∨ False)) ∨ p4) ∨ False) ∨ True) ∧ p3)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_196643234207551692945747209751 : ((p5 → (p3 → ((p2 ∧ (p2 ∧ p2)) → p2))) ∧ (((p3 ∨ p3) ∧ True) ∨ (True → ((p1 ∨ (p5 ∨ (p1 ∧ (p3 → p5)))) ∨ (False → p1))))) := by
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
  -- Conjunctions on the left can always be decomposed.
  let h6 := h5.left
  let h7 := h5.right
  -- One of the premise coincides with the conclusion.
  exact h7
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h8
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h9
  -- False on the left can always be used.
  apply False.elim h9



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_254877661338250117143768256824 : ((p4 ∧ True) → ((((((True ∧ p2) → (((p3 ∨ ((p3 ∨ p4) → p3)) ∧ p1) ∨ p4)) → True) → (p5 ∨ p5)) ∨ ((p4 ∨ False) → p4)) ∨ p1)) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Conjunctions on the left can always be decomposed.
  let h2 := h1.left
  let h3 := h1.right
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h4
  -- Disjunctions on the left can always be decomposed.
  cases h4
  case inl h5 =>
    -- One of the premise coincides with the conclusion.
    exact h5
  case inr h6 =>
    -- False on the left can always be used.
    apply False.elim h6



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_190559243311221720178000291744 : (((((p5 → p3) → (False ∨ p2)) → (False → False)) → p1) ∨ ((p2 ∧ ((p1 → p4) → False)) → ((((p2 ∧ (p1 → p1)) → p2) → True) → True))) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_139314169084904742707113614384 : (((True ∨ (p3 → ((p3 → p3) → (((p3 ∧ p1) ∨ (p3 ∧ p1)) ∧ (False ∧ ((True ∧ (p2 ∨ p5)) → p1)))))) ∨ p4) → (False ∨ (p3 ∨ True))) := by
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
      -- True on the right can always be proven directly.
      apply True.intro
    case inr h4 =>
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



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_111789661685525791599929312627 : (((((p5 ∧ p4) ∧ (False ∨ ((((p5 ∧ False) ∨ (True ∨ p1)) → ((p5 → p1) ∧ p5)) ∧ (p1 ∨ p5)))) ∨ (p4 ∨ False)) ∨ True) ∨ (p5 ∨ p2)) := by
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_147442277985878258465676626977 : ((((p3 → False) ∧ ((p4 ∨ ((True → ((p1 ∧ p1) → p3)) ∧ p3)) ∧ (False → ((p1 ∨ p3) ∨ p4)))) ∨ False) ∨ ((p2 → (True ∨ p4)) ∨ True)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_343237437228242995456923590287 : (p2 → ((False ∨ (p5 ∨ p1)) → (p2 → (((((((p4 ∨ p4) → False) → (p1 ∧ (p2 ∨ p5))) ∧ p1) ∨ p3) → ((True ∧ p1) → False)) ∨ True)))) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- Implications on the right can always be decomposed.
  intro h3
  -- Disjunctions on the left can always be decomposed.
  cases h2
  case inl h4 =>
    -- False on the left can always be used.
    apply False.elim h4
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
theorem thm_5_vars_59215399412194012052481838628 : (((p1 ∨ p5) ∨ (((p3 ∧ ((True → (((p4 ∧ (p2 ∧ (p4 ∧ (True ∧ p5)))) → (p2 → p3)) ∨ (p2 ∧ p3))) ∨ True)) ∨ True) ∨ p5)) ∨ p2) := by
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
theorem thm_5_vars_111468169069097026028065209135 : (((p1 → ((p5 ∧ ((p5 → (p2 ∨ ((True → p1) ∧ ((((p2 ∧ (p4 ∨ p2)) → p5) ∧ p3) ∨ p5)))) → p4)) ∧ p5)) ∧ p5) ∨ (False → p1)) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- Implications on the right can always be decomposed.
  intro h1
  -- False on the left can always be used.
  apply False.elim h1



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_44593431592016655850990673703 : ((((((p1 → (p1 ∧ (p3 → p2))) ∨ p1) ∧ p4) → (((((p2 → True) → p2) ∧ ((p5 ∧ (p4 ∨ True)) → p4)) → False) ∨ p2)) → p1) ∨ True) := by
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_661535490954660043002781043075 : (((((((False ∨ True) ∧ (((p4 → (((p2 → (p2 ∨ p5)) ∨ p3) → p4)) ∨ p2) ∨ p1)) → p2) ∨ (p1 → (False → p1))) → (p3 ∧ p2)) ∨ True) ∧ True) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the right disjunct based on <expert-advice>.
  apply Or.inr
  -- True on the right can always be proven directly.
  apply True.intro
  -- True on the right can always be proven directly.
  apply True.intro



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_76872613400551149081104575018 : (((((((True ∨ ((p4 ∨ p3) → p3)) ∧ p1) → p1) → False) ∨ (True ∧ (False → (p4 → (p2 ∧ (((p1 → p4) ∨ p1) ∨ p4)))))) → False) → p3) := by
  -- Implications on the right can always be decomposed.
  intro h1
  -- We want to use the implication h1 based on <expert-advice>. So we show its premise.
  have h2 : (((((True ∨ ((p4 ∨ p3) → p3)) ∧ p1) → p1) → False) ∨ (True ∧ (False → (p4 → (p2 ∧ (((p1 → p4) ∨ p1) ∨ p4)))))) := by
    -- Show the right disjunct based on <expert-advice>.
    apply Or.inr
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- True on the right can always be proven directly.
    apply True.intro
    -- Implications on the right can always be decomposed.
    intro h3
    -- Implications on the right can always be decomposed.
    intro h4
    -- Conjunctions on the right can always be decomposed.
    apply And.intro
    -- False on the left can always be used.
    apply False.elim h3
    -- False on the left can always be used.
    apply False.elim h3
  -- We have shown the premise of h1, we can now drive its conclusion.
  let h5 := h1 h2
  -- False on the left can always be used.
  apply False.elim h5



variable (p1 p2 p3 p4 p5 : Prop)
theorem thm_5_vars_154833112179490414336585374746 : ((((p3 ∨ p1) → (False ∧ ((True ∧ p2) ∧ (((p2 ∨ p5) ∨ (True ∧ p5)) → p4)))) → (p4 → p4)) ∧ (((True ∨ True) ∧ (p4 → True)) ∨ p2)) := by
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Implications on the right can always be decomposed.
  intro h1
  -- Implications on the right can always be decomposed.
  intro h2
  -- One of the premise coincides with the conclusion.
  exact h2
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- Conjunctions on the right can always be decomposed.
  apply And.intro
  -- Show the left disjunct based on <expert-advice>.
  apply Or.inl
  -- True on the right can always be proven directly.
  apply True.intro
  -- Implications on the right can always be decomposed.
  intro h3
  -- True on the right can always be proven directly.
  apply True.intro



